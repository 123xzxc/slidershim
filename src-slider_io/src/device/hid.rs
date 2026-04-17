use log::{error, info, warn};
use rusb::{self, DeviceHandle, GlobalContext};
use serialport::{DataBits, Parity, SerialPort, StopBits};
use std::{
  error::Error,
  io::{self, Read, Write},
  mem::swap,
  ops::{Deref, DerefMut},
  time::Duration,
};

use crate::{
  shared::{
    utils::{Buffer, ShimError},
    worker::ThreadJob,
  },
  state::{SliderInput, SliderLights, SliderState},
};

use super::config::HardwareSpec;

type HidReadCallback = fn(&Buffer, &mut SliderInput) -> ();
type HidLedCallback = fn(&mut Buffer, &mut Buffer, &SliderLights) -> ();

enum WriteType {
  Bulk,
  Interrupt,
}

pub struct HidJob {
  state: SliderState,

  vid: u16,
  pid: u16,
  read_endpoint: u8,
  led_endpoint: u8,
  disable_air: bool,

  read_callback: HidReadCallback,
  read_buf: Buffer,
  last_read_buf: Buffer,

  led_write_type: WriteType,
  led_callback: HidLedCallback,
  led_buf: Buffer,
  led_buf_two: Buffer,

  // --- 原生 USB (rusb) 专用 ---
  handle: Option<DeviceHandle<GlobalContext>>,

  // --- 串口通信专用 (Linnea) ---
  is_serial: bool,
  port: Option<Box<dyn SerialPort>>,
  packet_buf: [u8; 128],
  packet_len: usize,
  esc: bool,
  in_packet: bool,
}

impl HidJob {
  fn new(
    state: SliderState,
    vid: u16,
    pid: u16,
    read_endpoint: u8,
    led_endpoint: u8,
    disable_air: bool,
    read_callback: HidReadCallback,
    led_type: WriteType,
    led_callback: HidLedCallback,
  ) -> Self {
    Self {
      state,
      vid,
      pid,
      read_endpoint,
      led_endpoint,
      disable_air,
      read_callback,
      read_buf: Buffer::new(),
      last_read_buf: Buffer::new(),
      led_write_type: led_type,
      led_callback,
      led_buf: Buffer::new(),
      led_buf_two: Buffer::new(),
      handle: None,
      is_serial: false,
      port: None,
      packet_buf: [0; 128],
      packet_len: 0,
      esc: false,
      in_packet: false,
    }
  }

  // 模拟 C 语言中的 GetSerialPortByVidPid 功能
  fn find_serial_port(target_vid: u16, target_pid: u16) -> Option<String> {
    if let Ok(ports) = serialport::available_ports() {
      for port in ports {
        if let serialport::SerialPortType::UsbPort(info) = port.port_type {
          if info.vid == target_vid && info.pid == target_pid {
            return Some(port.port_name);
          }
        }
      }
    }
    None
  }

  pub fn from_config(state: &SliderState, spec: &HardwareSpec, disable_air: &bool) -> Self {
    match spec {
      HardwareSpec::TasollerOne => Self::new(
        state.clone(),
        0x1ccf,
        0x2333,
        0x84,
        0x03,
        *disable_air,
        |buf, input| {
          if buf.len != 11 {
            return;
          }

          let bits: Vec<u8> = buf
            .data
            .iter()
            .flat_map(|x| (0..8).map(move |i| ((x) >> i) & 1))
            .collect();
          for i in 0..32 {
            input.ground[i] = bits[34 + i] * 255;
          }
          input.flip_vert();

          input.air.copy_from_slice(&bits[28..34]);
          input.extra[0..2].copy_from_slice(&bits[26..28]);
        },
        WriteType::Bulk,
        |buf, _, lights| {
          buf.len = 240;
          buf.data[0] = 'B' as u8;
          buf.data[1] = 'L' as u8;
          buf.data[2] = '\x00' as u8;
          for (buf_chunk, state_chunk) in buf.data[3..96]
            .chunks_mut(3)
            .take(31)
            .zip(lights.ground.chunks(3).rev())
          {
            buf_chunk[0] = state_chunk[1];
            buf_chunk[1] = state_chunk[0];
            buf_chunk[2] = state_chunk[2];
          }
          buf.data[96..240].fill(0);
        },
      ),
      HardwareSpec::TasollerTwo => Self::new(
        state.clone(),
        0x1ccf,
        0x2333,
        0x84,
        0x03,
        *disable_air,
        |buf, input| {
          if buf.len != 36 {
            return;
          }

          input.ground.copy_from_slice(&buf.data[4..36]);
          input.flip_vert();

          let bits: Vec<u8> = (0..8).map(|x| (buf.data[3] >> x) & 1).collect();
          input.air.copy_from_slice(&bits[0..6]);
          input.extra[0..2].copy_from_slice(&bits[6..8]);
        },
        WriteType::Bulk,
        |buf, _, lights| {
          buf.len = 240;
          buf.data[0] = 'B' as u8;
          buf.data[1] = 'L' as u8;
          buf.data[2] = '\x00' as u8;
          for (buf_chunk, state_chunk) in buf.data[3..96]
            .chunks_mut(3)
            .take(31)
            .zip(lights.ground.chunks(3).rev())
          {
            buf_chunk[0] = state_chunk[1];
            buf_chunk[1] = state_chunk[0];
            buf_chunk[2] = state_chunk[2];
          }

          for (buf_chunks, state_chunk) in buf.data[96..240].chunks_mut(24).zip(
            lights
              .air_left
              .chunks(3)
              .rev()
              .chain(lights.air_right.chunks(3)),
          ) {
            for idx in 0..8 {
              buf_chunks[0 + idx * 3] = state_chunk[1];
              buf_chunks[1 + idx * 3] = state_chunk[0];
              buf_chunks[2 + idx * 3] = state_chunk[2];
            }
          }
        },
      ),
      HardwareSpec::LinneaLegacy => {
        let mut job = Self::new(
          state.clone(),
          0xaff1, // VID_AFF1
          0x52a4, // PID_52A4
          0, 0, *disable_air,
          |_, _| {}, // 串口模式在 tick 内独立解析，不使用通用的 read_callback
          WriteType::Bulk,
          |buf, _, lights| {
            // LED 组包逻辑复用通用框架
            buf.len = 100;
            buf.data[0] = 0xff;
            buf.data[1] = 0x02; // SLIDER_CMD_SET_LED
            buf.data[2] = 96;   // SIZE

            let mut checksum: u8 = 0u8.wrapping_add(0xff).wrapping_add(0x02).wrapping_add(96);
            for (i, val) in lights.ground.iter().enumerate().take(96) {
              let v = *val;
              buf.data[3 + i] = v;
              checksum = checksum.wrapping_add(v);
            }
            buf.data[99] = 0u8.wrapping_sub(checksum);
          },
        );
                job.is_serial = true;
        job
        // 【核心开关】将该任务标记为串口通信任务
      },
      HardwareSpec::Yuancon => Self::new(
        state.clone(),
        0x1973,
        0x2001,
        0x81,
        0x02,
        *disable_air,
        |buf, input| {
          if buf.len != 34 && buf.len != 35 {
            return;
          }

          input.ground.copy_from_slice(&buf.data[2..34]);
          for i in 0..6 {
            input.air[i ^ 1] = (buf.data[0] >> i) & 1;
          }
          for i in 0..3 {
            input.extra[2 - i] = (buf.data[1] >> i) & 1;
          }
        },
        WriteType::Interrupt,
        |buf, _, lights| {
          buf.len = 31 * 2;
          for (buf_chunk, state_chunk) in buf
            .data
            .chunks_mut(2)
            .take(31)
            .zip(lights.ground.chunks(3).rev())
          {
            buf_chunk[0] = (state_chunk[0] << 3 & 0xe0) | (state_chunk[2] >> 3);
            buf_chunk[1] = (state_chunk[1] & 0xf8) | (state_chunk[0] >> 5);
          }
        },
      ),
      HardwareSpec::YuanconThree => Self::new(
        state.clone(),
        0x0518,
        0x2022,
        0x83,
        0x03,
        *disable_air,
        |buf, input| {
          if buf.len != 46 { 
            return;
          }

          input.ground.copy_from_slice(&buf.data[2..34]);
          input.flip_vert();

          let bits: Vec<u8> = (0..8).map(|x| (buf.data[0] >> x) & 1).collect();
          for i in 0..6 {
            input.air[i ^ 1] = bits[i];
          }
          input.extra[0..2].copy_from_slice(&bits[6..8]);
        },
        WriteType::Interrupt,
        |buf, buf_two, lights| {
          buf.len = 61;
          buf.data[0] = 0;
          buf_two.len = 61;
          buf_two.data[0] = 1;

          for (buf_chunk, state_chunk) in buf.data[1..61]
              .chunks_mut(3)
              .zip(lights.ground.chunks(3).skip(11).take(20).rev())
          {
            buf_chunk[0] = state_chunk[0];
            buf_chunk[1] = state_chunk[1];
            buf_chunk[2] = state_chunk[2];
          }

          for (buf_chunk, state_chunk) in buf_two.data[1..34]
              .chunks_mut(3)
              .zip(lights.ground.chunks(3).take(11).rev())
          {
            buf_chunk[0] = state_chunk[0];
            buf_chunk[1] = state_chunk[1];
            buf_chunk[2] = state_chunk[2];
          }
        },
      ),
      HardwareSpec::Yubideck => Self::new(
        state.clone(),
        0x1973,
        0x2001,
        0x81,
        0x02,
        *disable_air,
        |buf, input| {
          if buf.len != 45 && buf.len != 46 {
            return;
          }

          input.ground.copy_from_slice(&buf.data[2..34]);
          input.flip_vert();
          for i in 0..6 {
            input.air[i ^ 1] = (buf.data[0] >> i) & 1;
          }
          for i in 0..3 {
            input.extra[2 - i] = (buf.data[1] >> i) & 1;
          }
        },
        WriteType::Interrupt,
        |buf, _, lights| {
          buf.len = 62;

          let lights_nibbles: Vec<u8> = lights
            .ground
            .chunks(3)
            .rev()
            .flat_map(|x| x.iter().map(|y| *y >> 4))
            .chain([
              lights.air_left[3] >> 4,
              lights.air_left[4] >> 4,
              lights.air_left[5] >> 4,
            ])
            .collect();

          for (buf_chunk, state_chunk) in buf
            .data
            .chunks_mut(3)
            .take(16)
            .zip(lights_nibbles.chunks(6))
          {
            buf_chunk[0] = (state_chunk[0]) | (state_chunk[1] << 4);
            buf_chunk[1] = (state_chunk[2]) | (state_chunk[3] << 4);
            buf_chunk[2] = (state_chunk[4]) | (state_chunk[5] << 4);
          }
        },
      ),
      HardwareSpec::YubideckThree => Self::new(
        state.clone(),
        0x1973,
        0x2001,
        0x81,
        0x02,
        *disable_air,
        |buf, input| {
          if buf.len != 45 && buf.len != 46 {
            return;
          }

          input.ground.copy_from_slice(&buf.data[2..34]);
          input.flip_vert();
          for i in 0..6 {
            input.air[i ^ 1] = (buf.data[0] >> i) & 1;
          }
          for i in 0..3 {
            input.extra[2 - i] = (buf.data[1] >> i) & 1;
          }
        },
        WriteType::Interrupt,
        |buf, buf_two, lights| {
          buf.len = 61;
          buf.data[0] = 0;
          buf_two.len = 61;
          buf_two.data[0] = 1;

          for (buf_chunk, state_chunk) in buf.data[1..61]
            .chunks_mut(3)
            .zip(lights.ground.chunks(3).skip(11).take(20).rev())
          {
            buf_chunk[0] = state_chunk[0];
            buf_chunk[1] = state_chunk[1];
            buf_chunk[2] = state_chunk[2];
          }

          for (buf_chunk, state_chunk) in buf_two.data[1..34]
            .chunks_mut(3)
            .zip(lights.ground.chunks(3).take(11).rev())
          {
            buf_chunk[0] = state_chunk[0];
            buf_chunk[1] = state_chunk[1];
            buf_chunk[2] = state_chunk[2];
          }

          buf_two.data[34..37].copy_from_slice(&lights.air_left[3..6]);
          buf_two.data[37..40].copy_from_slice(&lights.air_right[3..6]);
        },
      ),
    }
  }

  fn get_handle(&mut self) -> Result<(), Box<dyn Error>> {
    info!("Device finding vid {} pid {}", self.vid, self.pid);
    let handle = rusb::open_device_with_vid_pid(self.vid, self.pid);
    if handle.is_none() {
      error!("Device not found");
      return Err(Box::new(ShimError));
    }
    let mut handle = handle.unwrap();
    info!("Device found {:?}", handle);

    if handle.kernel_driver_active(0).unwrap_or(false) {
      info!("Device detaching kernel driver");
      handle.detach_kernel_driver(0)?;
    }
    info!("Device setting configuration");
    handle.set_active_configuration(1)?;

    info!("Device claiming interface");
    if self.vid == 0x0518 && self.pid == 0x2022 {
      handle.claim_interface(3)?;
    } else {
      handle.claim_interface(0)?;
    }

    self.handle = Some(handle);
    Ok(())
  }
}

const TIMEOUT: Duration = Duration::from_millis(20);

impl ThreadJob for HidJob {
  fn setup(&mut self) -> bool {
    // ---------------- 串口模式初始化 ----------------
    if self.is_serial {
        // 自动探测 COM 端口
        let port_name = Self::find_serial_port(self.vid, self.pid)
            .unwrap_or_else(|| "COM3".to_string());
        
        info!("Linnea Device connecting via Serial Port: {}", port_name);

        let port_result = serialport::new(&port_name, 115200)
            .data_bits(DataBits::Eight)
            .stop_bits(StopBits::One)
            .parity(Parity::None)
            .timeout(Duration::from_millis(5))
            .open();

        match port_result {
            Ok(mut p) => {
                // 1. 发送 DTR
                p.write_data_terminal_ready(true).ok();
                std::thread::sleep(Duration::from_millis(50));

                // 2. 发送激活指令
                p.write_all(&[0xff, 0x06, 0x00, 0xFB]).ok();
                std::thread::sleep(Duration::from_millis(10));
                p.write_all(&[0xff, 0x03, 0x00, 0xFE]).ok();
                
                info!("Linnea Serial Port setup successful");
                self.port = Some(p);
                return true;
            }
            Err(e) => {
                error!("Serial Port setup failed: {}", e);
                return false;
            }
        }
    }

    // ---------------- USB 原生模式初始化 ----------------
    match self.get_handle() {
      Ok(_) => {
        info!("Device OK");
        true
      }
      Err(e) => {
        error!("Device setup failed: {}", e);
        false
      }
    }
  }

  fn tick(&mut self) -> bool {
    let mut work = false;

    // =========================================================
    // 串口通信分支 (Linnea 专用)
    // =========================================================
    if self.is_serial {
        let port = match self.port.as_mut() {
            Some(p) => p,
            None => return false,
        };

        // --- 1. 读取传感器 ---
        let mut read_buf = [0u8; 128];
        if let Ok(bytes_read) = port.read(&mut read_buf) {
            if bytes_read > 0 {
                work = true;
                for &b in &read_buf[..bytes_read] {
                    if b == 0xff {
                        self.packet_len = 0;
                        self.packet_buf[self.packet_len] = 0xff;
                        self.packet_len += 1;
                        self.esc = false;
                        self.in_packet = true;
                        continue;
                    }
                    if !self.in_packet { continue; }
                    if self.packet_len == 1 {
                        self.packet_buf[self.packet_len] = b;
                        self.packet_len += 1;
                        continue;
                    }
                    if b == 0xfd {
                        self.esc = true;
                        continue;
                    }
                    if self.esc {
                        self.packet_buf[self.packet_len] = b.wrapping_add(1);
                        self.packet_len += 1;
                        self.esc = false;
                    } else {
                        self.packet_buf[self.packet_len] = b;
                        self.packet_len += 1;
                    }
                    if self.packet_len >= 128 {
                        self.in_packet = false;
                        continue;
                    }

                    // 包解析完毕
                    if self.packet_len >= 3 {
                        let payload_size = self.packet_buf[2] as usize;
                        if self.packet_len == 3 + payload_size + 1 {
                            if self.packet_buf[1] == 0x01 { // AUTO_SCAN
                                let mut input = self.state.input.lock();
                                input.ground.copy_from_slice(&self.packet_buf[3..35]);
                                input.ground.reverse();
                                if payload_size == 33 {
                                    let air_byte = self.packet_buf[35];
                                    for i in 0..6 { input.air[i] = (air_byte >> i) & 1; }
                                }
                                if self.disable_air {
                                    input.air.fill(0);
                                }
                            }
                            self.in_packet = false; 
                        }
                    }
                }
            }
        }

        // --- 2. 写入灯光 ---
        {
            let mut lights_handle = self.state.lights.lock();
            if lights_handle.dirty {
                // 复用组包回调，直接写到 led_buf
                (self.led_callback)(
                    &mut self.led_buf,
                    &mut self.led_buf_two,
                    lights_handle.deref(),
                );
                lights_handle.dirty = false;
            }
        }

if self.led_buf.len != 0 {
            // 【核心修复】：在发送给物理硬件前，最后一次检查并修正灯光方向
            if self.is_serial {
                // 创建一个临时缓冲区来存放翻转后的数据包
                let mut flip_buf = [0u8; 100];
                flip_buf.copy_from_slice(&self.led_buf.data[..100]);
                
                let mut new_checksum: u8 = 0u8.wrapping_add(0xff).wrapping_add(0x02).wrapping_add(96);
                
                // 按灯珠(3字节)为单位，左右对调位置
                for i in 0..32 {
                    let src_idx = 3 + (31 - i) * 3; // 取倒序的灯
                    let dst_idx = 3 + i * 3;        // 存入顺序的位置
                    
                    let b = self.led_buf.data[src_idx];
                    let r = self.led_buf.data[src_idx + 1];
                    let g = self.led_buf.data[src_idx + 2];
                    
                    flip_buf[dst_idx] = r;
                    flip_buf[dst_idx + 1] = g;
                    flip_buf[dst_idx + 2] = b;
                    
                    new_checksum = new_checksum.wrapping_add(r).wrapping_add(g).wrapping_add(b);
                }
                
                // 重新计算并更新校验和
                flip_buf[99] = 0u8.wrapping_sub(new_checksum);
                
                // 发送翻转后的包
                if port.write_all(&flip_buf).is_ok() {
                    self.led_buf.len = 0;
                }
            } else {
                // 非 Linnea 设备按原样发送
                if port.write_all(self.led_buf.slice()).is_ok() {
                    self.led_buf.len = 0;
                }
            }
        }

        return work;
    }

    // =========================================================
    // 原生 USB 通信分支 (Tasoller, Yuancon等)
    // =========================================================
    let handle = self.handle.as_mut().unwrap();

    {
      let res = handle
        .read_interrupt(self.read_endpoint, &mut self.read_buf.data, TIMEOUT)
        .map_err(|e| {
          e
        })
        .unwrap_or(0);
      self.read_buf.len = res;
      if (self.read_buf.len != 0) && (self.read_buf.slice() != self.last_read_buf.slice()) {
        work = true;
        let mut input_handle = self.state.input.lock();
        (self.read_callback)(&self.read_buf, input_handle.deref_mut());

        if self.disable_air {
          input_handle.air.fill(0);
        }
        swap(&mut self.read_buf, &mut self.last_read_buf);
      }
    }

    {
      {
        let mut lights_handle = self.state.lights.lock();
        if lights_handle.dirty {
          (self.led_callback)(
            &mut self.led_buf,
            &mut self.led_buf_two,
            lights_handle.deref(),
          );
          lights_handle.dirty = false;
        }
      }

      if self.led_buf.len != 0 {
        let res = (match self.led_write_type {
          WriteType::Bulk => handle.write_bulk(self.led_endpoint, self.led_buf.slice(), TIMEOUT),
          WriteType::Interrupt => {
            handle.write_interrupt(self.led_endpoint, &self.led_buf.slice(), TIMEOUT)
          }
        })
        .map_err(|e| {
          e
        })
        .unwrap_or(0);
        if res == self.led_buf.len + 1 {
          self.led_buf.len = 0;
        }
      }

      if self.led_buf_two.len != 0 {
        let res = (match self.led_write_type {
          WriteType::Bulk => {
            handle.write_bulk(self.led_endpoint, self.led_buf_two.slice(), TIMEOUT)
          }
          WriteType::Interrupt => {
            handle.write_interrupt(self.led_endpoint, &self.led_buf_two.slice(), TIMEOUT)
          }
        })
        .map_err(|e| {
          e
        })
        .unwrap_or(0);
        if res == self.led_buf_two.len + 1 {
          self.led_buf_two.len = 0;
        }
      }
    }

    work
  }
}

impl Drop for HidJob {
  fn drop(&mut self) {
    // 串口模式下 `self.port` 会自动 Drop 回收句柄，无需处理
    if !self.is_serial {
        if let Some(handle) = self.handle.as_mut() {
            handle.release_interface(0).ok();
        }
    }
  }
}
use fehler::throws;
use std::io::{stdout, Write};
use std::time::Instant;
use std::{io::stdin, sync::mpsc, thread};
use termion::event::Key;
use termion::input::TermRead;
use termion::raw::IntoRawMode;
use termion::screen::*;
use std::io::prelude::*;
use std::fs::File;
type Error = anyhow::Error;

// Fonts from 0x0..0xF
const FONT: [u8; 80] = [
    0xF0, 0x90, 0x90, 0x90, 0xF0, 0x20, 0x60, 0x20, 0x20, 0x70, 0xF0, 0x10, 0xF0, 0x80, 0xF0, 0xF0,
    0x10, 0xF0, 0x10, 0xF0, 0x90, 0x90, 0xF0, 0x10, 0x10, 0xF0, 0x80, 0xF0, 0x10, 0xF0, 0xF0, 0x80,
    0xF0, 0x90, 0xF0, 0xF0, 0x10, 0x20, 0x40, 0x40, 0xF0, 0x90, 0xF0, 0x90, 0xF0, 0xF0, 0x90, 0xF0,
    0x10, 0xF0, 0xF0, 0x90, 0xF0, 0x90, 0x90, 0xE0, 0x90, 0xE0, 0x90, 0xE0, 0xF0, 0x80, 0x80, 0x80,
    0xF0, 0xE0, 0x90, 0x90, 0x90, 0xE0, 0xF0, 0x80, 0xF0, 0x80, 0xF0, 0xF0, 0x80, 0xF0, 0x80, 0x80,
];

const KEYBOARD: [char; 16] = [
    '1', '2', '3', '4', 'q', 'w', 'e', 'r', 'a', 's', 'd', 'f', 'z', 'x', 'c', 'v',
];

struct Emulator {
    ram: [u8; 4096],
    vn: [u8; 16],
    dt: u8,
    st: u8,
    pc: u16,
    sp: u8,
    stack: [u16; 16],
    gfx: [u8; 64 * 32],
    sound: u8,
    delay: u8,
    i: u16,
    keyboard: [bool; 16],
    update: bool,
}

impl Emulator {
    fn new() -> Self {
        let mut ram = [0; 4096];
        FONT.into_iter().enumerate().for_each(|(i, v)| ram[i] = v);
        Self {
            ram,
            vn: [0; 16],
            dt: 0,
            st: 0,
            pc: 0x200,
            sp: 0,
            stack: [0; 16],
            gfx: [0; 64 * 32],
            sound: 0,
            delay: 0,
            i: 0,
            keyboard: [false; 16],
            update: true,
        }
    }

    fn load(&mut self, input: &[u8]) {
        assert!(input.len() < 0xFFFF - 0x200);
        input
            .into_iter()
            .enumerate()
            .for_each(|(i, v)| self.ram[0x200 + i] = *v);
    }

    fn cycle(&mut self) {
        let i = self.pc as usize;
        let input = (self.ram[i] as u16) << 8 | self.ram[i + 1] as u16;
        let slice = [
            (input & 0xF000) >> 12,
            (input & 0x0F00) >> 8,
            (input & 0x00F0) >> 4,
            input & 0x000F,
        ];
        eprintln!("Instruction {:#04x}: {:?}", input, slice);
        match slice {
            // 00E0 - CLS: Clear the display.
            [0x0, 0x0, 0xE, 0x0] => {
                self.gfx = [0; 64 * 32];
                self.update = true;
                self.pc += 2;
            }
            // 00EE - RET: The interpreter sets the program counter to the address at
            // the top of the stack, then subtracts 1 from the stack pointer.
            [0x0, 0x0, 0xE, 0xE] => {
                self.sp -= 1;
                self.pc = self.stack[self.sp as usize];
            }
            [0x0, _, _, _] => self.pc += 2,
            // 1nnn - JP addr: The interpreter sets the program counter to nnn.
            [0x1, nx, ny, nz] => self.pc = nx << 8 | ny << 4 | nz,
            // 2nnn - CALL addr: The interpreter increments the stack pointer, then
            // puts the current PC on the top of the stack. The PC is then set
            // to nnn.
            [0x2, nx, ny, nz] => {
                self.stack[self.sp as usize] = self.pc + 2;
                self.sp += 1;
                self.pc = nx << 8 | ny << 4 | nz;
            }
            // 3xkk - SE Vx, byte: The interpreter compares register Vx to kk,
            // and if they are equal, increments the program counter by 2.
            [0x3, x, kx, ky] => {
                if self.vn[x as usize] == (kx << 4 | ky) as u8 {
                    self.pc += 4;
                } else {
                    self.pc += 2;
                }
            }
            // 4xkk - SNE Vx, byte: The interpreter compares register Vx to kk,
            // and if they are not equal, increments the program counter by 2.
            [0x4, x, kx, ky] => {
                if self.vn[x as usize] != (kx << 4 | ky) as u8 {
                    self.pc += 4;
                } else {
                    self.pc += 2;
                }
            }
            // 5xy0 - SE Vx, Vy: The interpreter compares register Vx to register
            // Vy, and if they are equal, increments the program counter by 2.
            [0x5, x, y, 0x0] => {
                if self.vn[x as usize] == self.vn[y as usize] {
                    self.pc += 4;
                } else {
                    self.pc += 2;
                }
            }
            // 6xkk - LD Vx, byte: The interpreter puts the value kk into
            // register Vx.
            [0x6, x, kx, ky] => {
                self.vn[x as usize] = (kx << 4 | ky) as u8;
                self.pc += 2;
            }
            // 7xkk - ADD Vx, byte: Adds the value kk to the value of register
            // Vx, then stores the result in Vx.
            [0x7, x, kx, ky] => {
                self.vn[x as usize] = self.vn[x as usize] + (kx << 4 | ky) as u8;
                self.pc += 2;
            }
            // 8xy0 - LD Vx, Vy: Stores the value of register Vy in register Vx.
            [0x8, x, y, 0x0] => {
                self.vn[x as usize] = self.vn[y as usize];
                self.pc += 2;
            }
            // 8xy1 - OR Vx, Vy: Performs a bitwise OR on the values of Vx and
            // Vy, then stores the result in Vx.
            [0x8, x, y, 0x1] => {
                self.vn[x as usize] |= self.vn[y as usize];
                self.pc += 2;
            }
            // 8xy2 - AND Vx, Vy: Performs a bitwise AND on the values of Vx and
            // Vy, then stores the result in Vx.
            [0x8, x, y, 0x2] => {
                self.vn[x as usize] &= self.vn[y as usize];
                self.pc += 2;
            }
            // 8xy3 - XOR Vx, Vy: Performs a bitwise exclusive OR on the values
            // of Vx and Vy, then stores the result in Vx.
            [0x8, x, y, 0x3] => {
                self.vn[x as usize] ^= self.vn[y as usize];
                self.pc += 2;
            }
            // 8xy4 - ADD Vx, Vy: The values of Vx and Vy are added together. If
            // the result is greater than 8 bits (i.e., > 255,) VF is set to 1,
            // otherwise 0.
            [0x8, x, y, 0x4] => {
                let (sum, carry) = self.vn[x as usize].overflowing_add(self.vn[y as usize]);
                self.vn[0xF] = if carry { 1 } else { 0 };
                self.vn[x as usize] = sum;
                self.pc += 2;
            }
            // 8xy5 - SUB Vx, Vy: If Vx > Vy, then VF is set to 1, otherwise
            // 0. Then Vy is subtracted from Vx, and the results stored in Vx.
            [0x8, x, y, 0x5] => {
                let carry = self.vn[x as usize] > self.vn[y as usize];
                self.vn[0xF] = if carry { 1 } else { 0 };
                self.vn[x as usize] = self.vn[x as usize].wrapping_sub(self.vn[y as usize]);
                self.pc += 2;
            }
            // 8xy6 - SHR Vx {, Vy}: If the least-significant bit of Vx is 1,
            // then VF is set to 1, otherwise 0. Then Vx is divided by 2.
            [0x8, x, _, 0x6] => {
                self.vn[0xF] = self.vn[x as usize] & 0x1;
                self.vn[x as usize] >>= 1;
                self.pc += 2;
            }
            // 8xy7 - SUBN Vx, Vy: If Vy > Vx, then VF is set to 1, otherwise
            // 0. Then Vx is subtracted from Vy, and the results stored in Vx.
            [0x8, x, y, 0x7] => {
                let carry = self.vn[y as usize] > self.vn[x as usize];
                self.vn[0xF] = if carry { 1 } else { 0 };
                self.vn[x as usize] = self.vn[y as usize].wrapping_sub(self.vn[x as usize]);
                self.pc += 2;
            }
            // 8xyE - SHL Vx {, Vy}: If the most-significant bit of Vx is 1,
            // then VF is set to 1, otherwise to 0. Then Vx is multiplied by 2.
            [0x8, x, _, 0xE] => {
                self.vn[0xF] = (self.vn[x as usize] & 0x80) >> 7;
                self.vn[x as usize] <<= 1;
                self.pc += 2;
            }
            // 9xy0 - SNE Vx, Vy: The values of Vx and Vy are compared, and if
            // they are not equal, the program counter is increased by 2.
            [0x9, x, y, 0x0] => {
                if self.vn[x as usize] != self.vn[y as usize] {
                    self.pc += 4;
                } else {
                    self.pc += 2;
                }
            }
            // Annn - LD I, addr: The value of register I is set to nnn.
            [0xA, nx, ny, nz] => {
                self.i = nx >> 8 | ny >> 4 | nz;
                self.pc += 2;
            }
            // Bnnn - JP V0, addr: The program counter is set to nnn plus the
            // value of V0.
            [0xB, nx, ny, nz] => {
                self.pc = (nx >> 8 | ny >> 4 | nz) + self.vn[0x0] as u16;
            }
            // Cxkk - RND Vx, byte: The interpreter generates a random number
            // from 0 to 255, which is then ANDed with the value kk. The results
            // are stored in Vx.
            [0xC, x, kx, ky] => {
                let mut buffer = [0; 1];
                if getrandom::getrandom(&mut buffer).is_ok() {
                    self.vn[x as usize] = buffer[0] & (kx << 4 | ky) as u8;
                }
                self.pc += 2;
            }
            // Dxyn - DRW Vx, Vy, nibble: The interpreter reads n bytes from
            // memory, starting at the address stored in I. These bytes are
            // then displayed as sprites on screen at coordinates (Vx,
            // Vy). Sprites are XORed onto the existing screen. If this causes
            // any pixels to be erased, VF is set to 1, otherwise it is set to
            // 0. If the sprite is positioned so part of it is outside the
            // coordinates of the display, it wraps around to the opposite side
            // of the screen.
            [0xD, x, y, n] => {
                self.vn[0xF] = 0;
                for byte in 0..n {
                    let y = (self.vn[y as usize] + byte as u8) % 32;
                    for bit in 0..8 {
                        let x = (self.vn[x as usize] + bit) % 64;
                        let color = (self.ram[(self.i + byte as u16) as usize] >> (7 - bit)) & 0x1;
                        self.gfx[x as usize + (y as usize) * 64] ^= color;
                        self.vn[0xF] |= color & self.gfx[x as usize + (y as usize) * 64];
                    }
                }
                self.update = true;
                self.pc += 2;
            }
            // Ex9E - SKP Vx: Checks the keyboard, and if the key corresponding
            // to the value of Vx is currently in the down position, PC is
            // increased by 2.
            [0xE, x, 0x9, 0xE] => {
                if self.keyboard[self.vn[x as usize] as usize] {
                    self.pc += 4;
                } else {
                    self.pc += 2;
                }
            }
            // ExA1 - SKNP Vx: Checks the keyboard, and if the key corresponding
            // to the value of Vx is currently in the up position, PC is
            // increased by 2.
            [0xE, x, 0xA, 0x1] => {
                if !self.keyboard[self.vn[x as usize] as usize] {
                    self.pc += 4;
                } else {
                    self.pc += 2;
                }
            }
            // Fx07 - Ld Vx, DT: The value of DT is placed into Vx.
            [0xF, x, 0x0, 0x7] => {
                self.vn[x as usize] = self.dt;
                self.pc += 2;
            }
            // Fx0A - LD Vx, K: All execution stops until a key is pressed, then
            // the value of that key is stored in Vx.
            [0xF, x, 0x0, 0xA] => {
                for (i, key) in self.keyboard.iter().enumerate() {
                    if *key {
                        self.vn[x as usize] = i as u8;
                        self.pc += 2;
                        break;
                    }
                }
            }
            // Fx15 - LD DT, Vx: DT is set equal to the value of Vx.
            [0xF, x, 0x1, 0x5] => {
                self.dt = self.vn[x as usize];
                self.pc += 2;
            }
            // Fx18 - LD ST, Vx: ST is set equal to the value of Vx.
            [0xF, x, 0x1, 0x8] => {
                self.st = self.vn[x as usize];
                self.pc += 2;
            }
            // Fx1E - ADD I, Vx: The values of I and Vx are added, and the
            // results are stored in I.
            [0xF, x, 0x1, 0xE] => {
                self.i += self.vn[x as usize] as u16;
                self.vn[0xF] = if self.i > 0x0F00 { 1 } else { 0 };
                self.pc += 2;
            }
            // Fx29 - LD F, Vx: The value of I is set to the location for the
            // hexadecimal sprite corresponding to the value of Vx.
            [0xF, x, 0x2, 0x9] => {
                self.i = (self.vn[x as usize] as u16) * 5;
                self.pc += 2;
            }
            // Fx33 - LD B, Vx: The interpreter takes the decimal value of Vx,
            // and places the hundreds digit in memory at location in I, the
            // tens digit at location I+1, and the ones digit at location I+2.
            [0xF, x, 0x3, 0x3] => {
                self.ram[(self.i + 0) as usize] = self.vn[x as usize] / 100;
                self.ram[(self.i + 1) as usize] = self.vn[x as usize] % 100 / 10;
                self.ram[(self.i + 2) as usize] = self.vn[x as usize] % 10;
                self.pc += 2;
            }
            // Fx55 - LD [I], Vx: The interpreter copies the values of registers
            // V0 through Vx into memory, starting at the address in I. I is set
            // to I + X + 1 after operation.
            [0xF, x, 0x5, 0x5] => {
                for (i, value) in self.vn[..=x as usize].iter().enumerate() {
                    self.ram[self.i as usize + i] = *value;
                }
                self.i += x + 1;
                self.pc += 2;
            }
            // Fx65 - LD Vx, [I]: The interpreter reads values from memory
            // starting at location I into registers V0 through Vx. I is set to
            // I + X + 1 after operation.
            [0xF, x, 0x6, 0x5] => {
                for i in 0..=(x as usize) {
                    self.vn[i] = self.ram[self.i as usize + i];
                }
                self.pc += 2;
            }
            _ => todo!("Invalid opcode: {:#04x} as {:?}", input, slice),
        }
    }

    /// Returns true when program should beep
    fn tick(&mut self) -> bool {
        self.delay = self.delay.saturating_sub(1);
        self.sound = self.sound.saturating_sub(1);
        self.sound > 0
    }
}

impl Default for Emulator {
    fn default() -> Self {
        Self::new()
    }
}

enum Event {
    Key(char),
    Quit,
    Update,
    Tick,
}

#[throws]
fn main() {
    // Colorful messages
    color_backtrace::install();

    // Initialize emulator with rom
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if args.len() == 0 {
        println!("Usage: chip8 <rom>");
        return;
    }
    let mut file = File::open(&args[0])?;
    let mut rom = [0; 3584];
    file.read(&mut rom)?;
    let mut emulator = Emulator::new();
    emulator.load(&rom);

    // Initialize terminal
    let mut screen = AlternateScreen::from(stdout().into_raw_mode()?);
    write!(screen, "{}", termion::cursor::Hide)?;

    // Initialize channels
    let (tx, rx) = mpsc::channel();
    let (ty, tz) = (tx.clone(), tx.clone());

    // Initialize input
    thread::spawn(move || {
        let stdin = stdin();
        for key in stdin.keys() {
            match key {
                Ok(Key::Char(c)) if KEYBOARD.iter().any(|k| *k == c) => {
                    tx.send(Event::Key(c)).expect("Error when sending event");
                }
                Ok(Key::Ctrl('c')) => {
                    tx.send(Event::Quit).expect("Error when sending event");
                }
                _ => {}
            }
        }
    });

    // Initialize clock
    let mut update = Instant::now();
    thread::spawn(move || loop {
        if update.elapsed().as_millis() >= 2 {
            ty.send(Event::Update).expect("Error when sending event");
            update = Instant::now();
        }
    });

    // Initialize timer
    let mut timer = Instant::now();
    thread::spawn(move || loop {
        if timer.elapsed().as_millis() >= 16 {
            tz.send(Event::Tick).expect("Error when sending event");
            timer = Instant::now();
        }
    });

    'logic: loop {
        // Handle events
        match rx.recv()? {
            Event::Key(c) => {
                if let Some(index) = KEYBOARD.iter().position(|k| *k == c) {
                    // Reset keyboard
                    emulator.keyboard.iter_mut().for_each(|k| *k = false);
                    emulator.keyboard[index] = true;
                }
            }
            Event::Quit => break 'logic,
            Event::Tick => {
                if emulator.tick() {
                    // Beep
                    write!(screen, "\x07")?;
                }
            }
            Event::Update => {
                // Do next cycle
                emulator.cycle();

                // Draw on change
                if emulator.update {
                    write!(screen, "{}", termion::clear::All)?;
                    for (i, chunk) in emulator.gfx.chunks(64).enumerate() {
                        write!(screen, "{}", termion::cursor::Goto(1, 1 + i as u16))?;
                        for bit in chunk {
                            let color = if *bit != 0 { 5 } else { 0 };
                            write!(
                                screen,
                                "{}{}█",
                                termion::color::Fg(termion::color::AnsiValue::rgb(color, color, color)),
                                termion::color::Bg(termion::color::Black)
                            )?;
                        }
                    }
                    screen.flush()?;
                    emulator.update = false;
                }
            }
        }
    }
    write!(screen, "{}", termion::cursor::Show)?;
}

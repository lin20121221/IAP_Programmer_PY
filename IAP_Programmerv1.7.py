import tkinter as tk
from tkinter import filedialog, messagebox
import customtkinter
from customtkinter import CTk, CTkComboBox, CTkEntry, CTkButton, CTkLabel, CTkProgressBar, CTkToplevel, CTkFrame
from tkinterdnd2 import DND_FILES, TkinterDnD
import serial.tools.list_ports
import serial
import threading
import time
import os
import struct
import binascii
import re
from ctypes import windll

# --- 强制开启 Windows 高 DPI 意识，防止系统模糊缩放 ---
try:
    windll.shcore.SetProcessDpiAwareness(1)
except:
    pass

# Global CustomTkinter settings
customtkinter.set_appearance_mode("light")
customtkinter.set_default_color_theme("green")
# 彻底禁用 customtkinter 的自动缩放影响
customtkinter.deactivate_automatic_dpi_awareness()

class ProgressBarDialog(CTkToplevel):
    """进度条对话框"""
    def __init__(self, parent):
        super().__init__(parent)
        self.title("下载进度")
        self.geometry("350x120")
        self.resizable(False, False)
        self.attributes('-topmost', True)
        self.protocol("WM_DELETE_WINDOW", lambda: None)
        
        # 居中显示
        self.center_on_parent(parent)
        
        self.grab_set()
        self.transient(parent)
        
        self.frame = CTkFrame(self)
        self.frame.pack(padx=20, pady=20, fill="both", expand=True)
        
        self.label_operation = CTkLabel(self.frame, text="正在传输数据...", font=("Verdana", 14))  # 12->14
        self.label_operation.pack(pady=(0, 10))
        
        self.progress_bar = CTkProgressBar(self.frame, width=280)
        self.progress_bar.pack(pady=(0, 5))
        self.progress_bar.set(0)
        
        self.label_percent = CTkLabel(self.frame, text="0%", font=("Verdana", 13))  # 11->13
        self.label_percent.pack()
        
    def center_on_parent(self, parent):
        """将窗口居中显示在父窗口上"""
        # 更新窗口以确保获取正确的尺寸
        self.update_idletasks()
        
        # 获取父窗口位置和尺寸
        parent_x = parent.winfo_x()
        parent_y = parent.winfo_y()
        parent_width = parent.winfo_width()
        parent_height = parent.winfo_height()
        
        # 获取对话框尺寸
        dialog_width = self.winfo_width()
        dialog_height = self.winfo_height()
        
        # 计算居中位置
        x = parent_x + (parent_width - dialog_width) // 2
        y = parent_y + (parent_height - dialog_height) // 2
        
        # 设置位置
        self.geometry(f"+{x}+{y}")
        
    def set_operation_info(self, text: str):
        self.label_operation.configure(text=text)
        self.update()
        
    def set_progress(self, current: int, total: int):
        """设置进度条 - 修复了参数顺序问题"""
        if total <= 0:
            return
            
        # 确保进度在0-100范围内
        if current > total:
            current = total
        if current < 0:
            current = 0
            
        percent = int((current / total) * 100)
        value = current / total if total > 0 else 0
        
        self.progress_bar.set(value)
        self.label_percent.configure(text=f"{percent}%")
        self.update()
        
    def close_bar(self):
        self.grab_release()
        self.destroy()

class IAPProgrammer:
    def __init__(self):
        self.root = TkinterDnD.Tk()
        self.root.title("IAP_Programmer_V1.7")
        self.root.geometry("1080x500")
        self.root.resizable(False, False)
        self.root.configure(bg="#778899")
        
        # 强制设置 CTK 缩放因子
        customtkinter.set_widget_scaling(1.0)
        customtkinter.set_window_scaling(1.0)
        
        self.serial_port = None
        self.lock = threading.Lock()
        self.m_InitFlag = True
        self.m_PortNameSelectUART = 0
        self.init_thread = None
        self.BinAddr = ""
        self.file_data_list = []
        self.file_extension = ""
        self.file_min_address = 0xFFFFFFFF  # 记录HEX文件的最小地址
        
        # 预计算CRC表（提高计算速度）
        self.crc_table = self._generate_crc32_table()
        
        # 用于存储当前设备列表，用于比较
        self.current_devices = []
        
        self.main_frame = CTkFrame(self.root, fg_color="#778899", corner_radius=0)
        self.main_frame.pack(fill="both", expand=True)
        
        self.setup_ui()
        self.setup_drag_and_drop()
        self.start_init_thread()
        
        # 绑定窗口关闭事件
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)
        
    def _generate_crc32_table(self):
        """生成CRC32查表法需要的256个表项"""
        crc_table = []
        for i in range(256):
            crc = i
            for _ in range(8):
                if crc & 1:
                    crc = (crc >> 1) ^ 0xEDB88320
                else:
                    crc >>= 1
            crc_table.append(crc & 0xFFFFFFFF)
        return crc_table
        
    def get_load_file_crc(self, data, initial_crc=0):
        """使用查表法计算CRC32（速度更快，结果与原来完全一致）"""
        crc = initial_crc
        for byte in data:
            crc = (crc >> 8) ^ self.crc_table[(crc ^ byte) & 0xFF]
            crc &= 0xFFFFFFFF
        return crc
        
    def setup_ui(self):
        """设置UI界面 - 使用第一个文件的布局"""
        # UART Port
        self.label_uart_port = CTkLabel(self.main_frame, text="UART Port", font=("Verdana", 16),  # 14->16
                                       fg_color="#778899", text_color="#000000")
        self.label_uart_port.place(x=30, y=90)
        
        self.combo_port_name = CTkComboBox(self.main_frame, values=[], font=("Verdana", 14), width=425,  # 12->14
                                          state="readonly", fg_color="#F0F0F0", text_color="#000000", 
                                          dropdown_fg_color="#F0F0F0")
        self.combo_port_name.place(x=160, y=86)
        
        # Baud Rate
        self.label_baud_rate = CTkLabel(self.main_frame, text="Baud Rate", font=("Verdana", 16),  # 14->16
                                       fg_color="#778899", text_color="#000000")
        self.label_baud_rate.place(x=620, y=90)
        
        self.combo_baud_rate = CTkComboBox(self.main_frame, values=["110", "300", "600", "1200", "2400", "4800", "9600", 
                                                         "14400", "19200", "38400", "57600", "115200", "128000", 
                                                         "230400", "256000", "460800", "921600", "1228800", "1382400"], 
                                          font=("Verdana", 14), width=290, state="readonly",  # 12->14
                                          fg_color="#F0F0F0", text_color="#000000", dropdown_fg_color="#F0F0F0")
        self.combo_baud_rate.place(x=740, y=86)
        self.combo_baud_rate.set("115200")
        
        # File Path
        self.text_file_path = CTkEntry(self.main_frame, font=("Verdana", 14), width=800, height=40,  # 12->14
                                       fg_color="#F0F0F0", text_color="#000000",
                                       corner_radius=0, placeholder_text="Drag and drop file here or click '...' to browse")
        self.text_file_path.place(x=35, y=355)
        
        # 绑定只读属性
        self.text_file_path.bind("<Key>", lambda e: "break")
            
        self.button_open_file = CTkButton(self.main_frame, text=".....", font=("Verdana", 12),  # 10->12
                                         width=55, height=40, fg_color="#F0F0F0", 
                                         text_color="#000000", hover_color="#E0E0E0",
                                         corner_radius=0, command=self.open_file_dialog)
        self.button_open_file.place(x=980, y=355)
        
        # Data Start Address (HEX)
        self.label_start_address = CTkLabel(self.main_frame, text="Data Start Address (HEX)", 
                                           font=("Verdana", 16), fg_color="#778899",  # 14->16
                                           text_color="#000000")
        self.label_start_address.place(x=30, y=188)
        
        self.text_start_address = CTkEntry(self.main_frame, font=("Verdana", 14), width=412,  # 12->14
                                          fg_color="#F0F0F0", text_color="#000000", 
                                          corner_radius=0, justify="center")
        self.text_start_address.place(x=320, y=188)
        self.text_start_address.insert(0, "08010000")
        self.text_start_address.bind("<KeyPress>", self.on_hex_keypress)
        
        # Data Length
        self.label_data_length = CTkLabel(self.main_frame, text="Data Length", font=("Verdana", 16),  # 14->16
                                         fg_color="#778899", text_color="#000000")
        self.label_data_length.place(x=30, y=269)
        
        self.text_data_length = CTkEntry(self.main_frame, font=("Verdana", 14), width=241,  # 12->14
                                        state="readonly", fg_color="#F0F0F0", 
                                        text_color="#000000", corner_radius=0, justify="center")
        self.text_data_length.place(x=170, y=265)
        self.text_data_length.insert(0, "0 Bytes")
        
        # Data CRC
        self.label_data_crc = CTkLabel(self.main_frame, text="Data CRC", font=("Verdana", 16),  # 14->16
                                      fg_color="#778899", text_color="#000000")
        self.label_data_crc.place(x=430, y=269)
        
        self.text_data_crc = CTkEntry(self.main_frame, font=("Verdana", 14), width=169,  # 12->14
                                     state="readonly", fg_color="#F0F0F0", 
                                     text_color="#000000", corner_radius=0, justify="center")
        self.text_data_crc.place(x=560, y=265)
        self.text_data_crc.insert(0, "0x00000000")
        
        # Download Button
        self.button_download = CTkButton(self.main_frame, text="Download", font=("Verdana", 16, "bold"),  # 14->16
                                        width=238, height=112, fg_color="#F0F0F0", 
                                        text_color="#004040", hover_color="#E0E0E0", corner_radius=0,
                                        command=self.start_download)
        self.button_download.place(x=795, y=188)
        
    def setup_drag_and_drop(self):
        """设置拖放功能 - 使用tkinterdnd2"""
        try:
            self.root.drop_target_register(DND_FILES)
            self.root.dnd_bind('<<Drop>>', self.on_file_drop)
        except Exception as e:
            print(f"Drag-and-drop setup error: {e}")
            
    def on_file_drop(self, event):
        """当文件被拖放到窗口时调用"""
        try:
            # 获取文件路径（处理可能的格式）
            path = event.data.strip('{}').strip('"')
            if os.path.isfile(path):
                # 更新文件路径显示
                self.text_file_path.delete(0, tk.END)
                self.text_file_path.insert(0, path)
                self.process_file(path)
        except Exception as e:
            print(f"Error handling file drop: {e}")
            
    def on_hex_keypress(self, event):
        char = event.char.upper()
        if char and (char not in "0123456789ABCDEF" and event.keysym != "BackSpace"):
            return "break"
            
    def open_file_dialog(self):
        file_path = filedialog.askopenfilename(
            filetypes=[
                ("Supported Files", "*.bin;*.hex"),
                ("Intel BIN Files", "*.bin"),
                ("Hex Files", "*.hex"),
                ("All Files", "*.*")
            ],
            title="Open File"
        )
        
        if file_path:
            self.text_file_path.delete(0, tk.END)
            self.text_file_path.insert(0, file_path)
            self.process_file(file_path)
            
    def process_file(self, file_path: str):
        """处理文件 - 使用第二个文件的CRC计算逻辑"""
        try:
            ext = os.path.splitext(file_path)[1].upper()
            self.file_extension = ext
            self.file_min_address = 0xFFFFFFFF  # 重置最小地址
            
            if ext not in [".BIN", ".HEX"]:
                messagebox.showerror("Error", "The download file format error")
                return
                
            if not os.path.exists(file_path): 
                return
                
            self.file_data_list = []
            datalength, crc = 0, 0
            
            try:
                if ext == ".HEX":
                    with open(file_path, 'r') as f:
                        seg, last, p_len = 0, 0, 2048
                        current_block = None
                        min_address = 0xFFFFFFFF
                        
                        for line in f:
                            if not line.startswith(':'): 
                                continue
                            rt = line[7:9]
                            if rt == "04": 
                                seg = int(line[9:13], 16) << 16
                            elif rt == "00":
                                l, off = int(line[1:3], 16), int(line[3:7], 16)
                                addr = seg + off
                                
                                # 更新最小地址
                                if addr < min_address:
                                    min_address = addr
                                
                                datalength += l
                                
                                # 检查是否需要新块
                                if current_block is None or (addr - current_block["addr"]) >= 2048 or p_len >= 2048:
                                    if current_block is not None:
                                        self.file_data_list.append(current_block)
                                    
                                    current_block = {
                                        "addr": addr,
                                        "data": bytearray([0xFF] * 2048)
                                    }
                                    p_len = 0
                                
                                # 解析数据
                                data_hex = binascii.unhexlify(line[9:9+l*2])
                                for b in data_hex:
                                    if p_len < 2048:  # 确保不超过块大小
                                        current_block["data"][p_len] = b
                                        p_len += 1
                                        crc = self.get_load_file_crc([b], crc)  # 使用查表法CRC
                                    else:
                                        # 如果当前块已满，创建新块
                                        self.file_data_list.append(current_block)
                                        current_block = {
                                            "addr": addr,
                                            "data": bytearray([0xFF] * 2048)
                                        }
                                        current_block["data"][0] = b
                                        p_len = 1
                                        crc = self.get_load_file_crc([b], crc)  # 使用查表法CRC
                                
                                last = addr + l
                        
                        # 添加最后一个块
                        if current_block is not None:
                            self.file_data_list.append(current_block)
                        
                        # 更新起始地址为HEX文件的最小地址
                        if self.file_data_list and min_address != 0xFFFFFFFF:
                            self.text_start_address.delete(0, tk.END)
                            self.text_start_address.insert(0, f"{min_address:08X}")
                            
                else:  # BIN文件
                    with open(file_path, 'rb') as f:
                        content = f.read()
                        datalength = len(content)
                        
                        for i in range(0, datalength, 2048):
                            chunk = content[i:i+2048]
                            block = bytearray(chunk)
                            if len(block) < 2048: 
                                block.extend([0xFF]*(2048-len(block)))
                            self.file_data_list.append({"addr": i, "data": block})
                            crc = self.get_load_file_crc(chunk, crc)  # 使用查表法CRC
                            
                # 更新UI显示
                self.text_data_length.configure(state="normal")
                self.text_data_length.delete(0, tk.END)
                self.text_data_length.insert(0, f"{datalength} Bytes")
                self.text_data_length.configure(state="readonly")
                
                self.text_data_crc.configure(state="normal")
                self.text_data_crc.delete(0, tk.END)
                self.text_data_crc.insert(0, f"0x{crc:08X}")
                self.text_data_crc.configure(state="readonly")
                
                print(f"Loaded {len(self.file_data_list)} blocks, total {datalength} bytes, CRC: 0x{crc:08X}")
                
            except Exception as e:
                print(f"Error processing file: {e}")
                messagebox.showerror("Error", f"Failed to process file: {str(e)}")
                
        except Exception as e:
            messagebox.showerror("Error", f"Failed to process file: {str(e)}")
            
    def start_init_thread(self):
        self.init_thread = threading.Thread(target=self.init_device_thread, daemon=True)
        self.init_thread.start()
        
    def init_device_thread(self):
        while self.m_InitFlag:
            self.init_device()
            time.sleep(1)
            
    def init_device(self):
        """初始化设备"""
        with self.lock:
            self.init_rs232_port_name()
            
    def mul_get_hardware_info(self, hard_type: str, prop_key: str) -> list:
        """获取硬件信息"""
        device_list = []
        try:
            ports = serial.tools.list_ports.comports()
            for port in ports:
                if port.description:
                    device_list.append(f"{port.description} ({port.device})")
                else:
                    device_list.append(port.device)
            return device_list
        except Exception as e:
            print(f"Error getting hardware info: {e}")
            return []
            
    def init_rs232_port_name(self):
        """初始化串口列表"""
        str_list = self.mul_get_hardware_info("Win32_SerialPort", "Name")
        
        # 检查设备列表是否有变化
        if not self.current_devices or set(str_list) != set(self.current_devices):
            self.current_devices = str_list
            
            # 更新下拉框
            self.combo_port_name.configure(values=str_list)
            
            if str_list:
                if self.m_PortNameSelectUART < len(str_list):
                    try:
                        self.combo_port_name.set(str_list[self.m_PortNameSelectUART])
                    except:
                        self.combo_port_name.set(str_list[0])
                else:
                    self.combo_port_name.set(str_list[0])
            else:
                self.combo_port_name.set("")
                
    def start_download(self):
        if not self.text_file_path.get():
            messagebox.showerror("Error", "Can't open the download file")
            return
            
        if not self.file_data_list:
            messagebox.showerror("Error", "Please select a valid file first")
            return
            
        download_thread = threading.Thread(target=self.download_thread_rs232, daemon=True)
        download_thread.start()
        
    def download_thread_rs232(self):
        """下载线程 - 使用第二个文件的下载逻辑"""
        with self.lock:
            # 创建进度对话框
            progress_dialog = ProgressBarDialog(self.root)
            
            # 在新线程中显示对话框
            def show_progress_dialog():
                progress_dialog.set_operation_info("Downloading.......")
                progress_dialog.set_progress(0, 100)  # 初始0%
            
            threading.Thread(target=show_progress_dialog, daemon=True).start()
            time.sleep(0.1)  # 给对话框显示时间
            
            ser = None
            try:
                # 打开串口
                port_match = re.search(r'COM\d+', self.combo_port_name.get(), re.IGNORECASE)
                if not port_match:
                    raise Exception("Invalid COM port selected")
                    
                port_name = port_match.group()
                baud_rate = int(self.combo_baud_rate.get())
                
                ser = serial.Serial(
                    port=port_name,
                    baudrate=baud_rate,
                    bytesize=8,
                    parity=serial.PARITY_NONE,
                    stopbits=serial.STOPBITS_ONE,
                    timeout=1.5
                )
                ser.reset_input_buffer()
                
                total_blocks = len(self.file_data_list)
                
                # 1. 握手
                progress_dialog.set_progress(5, 100)  # 5%
                ser.write(b'\x5A\xA5')
                if ser.read(2) != b'\xCC\xDD': 
                    raise Exception("Handshake timeout")
                time.sleep(0.8)
                
                # 2. 开始
                progress_dialog.set_progress(10, 100)  # 10%
                ser.write(b'\x5A\x01')
                if ser.read(2) != b'\xCC\xDD': 
                    raise Exception("Mode entry failed")
                
                # 3. 数据发送
                ui_base_addr = int(self.text_start_address.get(), 16)
                
                for i, block in enumerate(self.file_data_list):
                    # 计算目标地址
                    if self.file_extension == ".HEX":
                        # 对于HEX文件，使用块中的绝对地址
                        target_addr = block["addr"]
                    else:
                        # 对于BIN文件，使用基础地址 + 块偏移
                        target_addr = ui_base_addr + block["addr"]
                    
                    # 构建数据包
                    packet = bytearray([0x31])  # 数据包起始标志
                    packet.extend(struct.pack(">I", target_addr))  # 大端序地址
                    packet.extend(block["data"])  # 2048字节数据
                    
                    # 计算校验和（包括地址字节和数据）
                    checksum = sum(packet[1:2053]) & 0xFF
                    packet.append(checksum)
                    
                    # 发送数据包
                    ser.write(packet)
                    if ser.read(2) != b'\xCC\xDD':
                        raise Exception(f"Block {i} address {hex(target_addr)} checksum error")
                    
                    # 更新进度 - 从10%到90%
                    progress = 10 + int((i + 1) * 80 / total_blocks)
                    progress_dialog.set_progress(progress, 100)
                
                # 4. 结束
                progress_dialog.set_progress(95, 100)  # 95%
                ser.write(b'\x5A\x02')
                ser.read(2)  # 读取响应
                
                progress_dialog.set_progress(100, 100)  # 100%
                time.sleep(0.5)
                progress_dialog.close_bar()
                
                messagebox.showinfo("Success", "Download succeed!")
                
            except Exception as e:
                progress_dialog.close_bar()
                messagebox.showerror("Error", f"Download failed: {str(e)}")
            finally:
                if ser and ser.is_open:
                    ser.close()
                    
    def on_closing(self):
        self.m_InitFlag = False
        
        if self.init_thread and self.init_thread.is_alive():
            time.sleep(0.1)
            
        self.root.destroy()

def main():
    app = IAPProgrammer()
    app.root.mainloop()

if __name__ == "__main__":
    main()
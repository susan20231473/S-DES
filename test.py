import tkinter as tk
from tkinter import ttk, messagebox
import time
import threading
import random

# -------------------------- S-DES核心算法定义 --------------------------
# 置换表定义（修正后，与图示完全一致）
IP = [2, 6, 3, 1, 4, 8, 5, 7]  # 初始置换
IP_INV = [4, 1, 3, 5, 7, 2, 8, 6]  # 逆初始置换
E = [4, 1, 2, 3, 2, 3, 4, 1]  # 扩展置换
P = [2, 4, 3, 1]  # P盒置换(SPBox)
P10 = [3, 5, 2, 7, 4, 10, 1, 9, 8, 6]  # 10位密钥置换（修正后）
P8 = [6, 3, 7, 4, 8, 5, 10, 9]  # 8位密钥置换（修正后）

# S盒定义
S0 = [
    [1, 0, 3, 2],
    [3, 2, 1, 0],
    [0, 2, 1, 3],
    [3, 1, 0, 2]
]

S1 = [
    [0, 1, 2, 3],
    [2, 3, 1, 0],
    [3, 0, 1, 2],
    [2, 1, 0, 3]
]


def permute(bits, table):
    """按置换表对二进制位进行置换"""
    return [bits[i - 1] for i in table]


def left_shift(bits, n=1):
    """循环左移n位"""
    return bits[n:] + bits[:n]


def generate_keys(key):
    """生成子密钥K1和K2（10位密钥→两个8位子密钥）"""
    key_p10 = permute(key, P10)
    c0, d0 = key_p10[:5], key_p10[5:]
    c1 = left_shift(c0, 1)
    d1 = left_shift(d0, 1)
    k1 = permute(c1 + d1, P8)
    c2 = left_shift(c1, 2)
    d2 = left_shift(d1, 2)
    k2 = permute(c2 + d2, P8)
    return k1, k2


def f_function(r, key):
    """F函数：扩展→异或→S盒→P盒(SPBox)"""
    expanded = permute(r, E)
    xor_result = [expanded[i] ^ key[i] for i in range(8)]
    left, right = xor_result[:4], xor_result[4:]
    row = left[0] * 2 + left[3]
    col = left[1] * 2 + left[2]
    s0_out = [int(bit) for bit in f"{S0[row][col]:02b}"]
    row = right[0] * 2 + right[3]
    col = right[1] * 2 + right[2]
    s1_out = [int(bit) for bit in f"{S1[row][col]:02b}"]
    return permute(s0_out + s1_out, P)


def sdes_encrypt(plaintext, key):
    """加密：8位明文+10位密钥→8位密文（修正版，包含显式SW操作）"""
    k1, k2 = generate_keys(key)
    ip_out = permute(plaintext, IP)
    l0, r0 = ip_out[:4], ip_out[4:]

    # 第一轮
    f1 = f_function(r0, k1)
    l1 = [l0[i] ^ f1[i] for i in range(4)]
    r1 = r0

    # 交换左右部分（SW操作）
    l1, r1 = r1, l1

    # 第二轮
    f2 = f_function(r1, k2)
    l2 = [l1[i] ^ f2[i] for i in range(4)]
    r2 = r1

    # 最后不需要再交换，直接合并后做逆初始置换
    return permute(l2 + r2, IP_INV)


def sdes_decrypt(ciphertext, key):
    """解密：8位密文+10位密钥→8位明文（与修正后的加密流程对应）"""
    k1, k2 = generate_keys(key)
    ip_out = permute(ciphertext, IP)
    l0, r0 = ip_out[:4], ip_out[4:]

    # 第一轮（使用k2）
    f1 = f_function(r0, k2)
    l1 = [l0[i] ^ f1[i] for i in range(4)]
    r1 = r0

    # 交换左右部分（SW操作）
    l1, r1 = r1, l1

    # 第二轮（使用k1）
    f2 = f_function(r1, k1)
    l2 = [l1[i] ^ f2[i] for i in range(4)]
    r2 = r1

    # 最后不需要再交换
    return permute(l2 + r2, IP_INV)


# -------------------------- 数据格式转换工具 --------------------------
def str_to_bits(s):
    """字符串→8位二进制列表（按ASCII编码，每组1字节）"""
    bits = []
    for c in s:
        byte = [int(bit) for bit in f"{ord(c):08b}"]
        bits.extend(byte)
    return bits


def bits_to_str(bits):
    """8位二进制列表→字符串（按ASCII编码）"""
    str_result = ""
    for i in range(0, len(bits), 8):
        byte = bits[i:i + 8]
        if len(byte) < 8:
            break
        value = int("".join(map(str, byte)), 2)
        str_result += chr(value)
    return str_result


def int_to_bits(n, length):
    """整数→指定长度的二进制列表（不足补0）"""
    return [int(bit) for bit in f"{n:0{length}b}"]


def bits_to_int(bits):
    """二进制列表→整数"""
    return int("".join(map(str, bits)), 2)


# -------------------------- 填充方案实现 --------------------------
def pkcs7_pad(data_bytes, block_size=8):
    """PKCS#7填充：对字节数据进行填充"""
    padding_length = block_size - (len(data_bytes) % block_size)
    padding = bytes([padding_length] * padding_length)
    return data_bytes + padding


def pkcs7_unpad(data_bytes):
    """PKCS#7去填充"""
    if not data_bytes:
        return b""
    padding_length = data_bytes[-1]
    if padding_length <= 0 or padding_length > len(data_bytes):
        raise ValueError("无效的填充")
    # 检查填充字节是否都正确
    for i in range(1, padding_length):
        if data_bytes[-i - 1] != padding_length:
            raise ValueError("无效的填充")
    return data_bytes[:-padding_length]


# -------------------------- 完整性校验 --------------------------
def calculate_checksum(data_bytes):
    """计算简单校验和：所有字节的异或"""
    checksum = 0
    for byte in data_bytes:
        checksum ^= byte
    return bytes([checksum])


# -------------------------- 暴力破解实现 --------------------------
class BruteForce:
    def __init__(self, plaintext, ciphertext, progress_callback=None):
        self.plaintext = plaintext
        self.ciphertext = ciphertext
        self.found_keys = []
        self.progress_callback = progress_callback
        self.start_time = 0
        self.end_time = 0
        self.running = True  # 用于控制是否继续运行

    def stop(self):
        """停止破解过程"""
        self.running = False

    def run(self):
        """执行暴力破解（遍历所有10位密钥）"""
        self.start_time = time.time()
        total = 1024
        for i in range(total):
            if not self.running:
                break

            key = int_to_bits(i, 10)
            encrypted = sdes_encrypt(self.plaintext, key)
            if encrypted == self.ciphertext:
                self.found_keys.append(key)
            if self.progress_callback and i % 2 == 0:
                self.progress_callback(i / total * 100)

        self.end_time = time.time()

    def get_result(self):
        """返回破解结果：密钥列表和耗时"""
        duration = self.end_time - self.start_time
        keys_str = [bits_to_int(key) for key in self.found_keys]
        return {
            "keys": keys_str,
            "count": len(self.found_keys),
            "time": round(duration, 4),
            "completed": self.running
        }


# -------------------------- GUI界面实现 --------------------------
class SDesGUI:
    def __init__(self, root):
        self.root = root
        self.root.title("S-DES加密解密工具")
        self.root.geometry("750x600")
        self.root.resizable(False, False)

        # 设置窗口背景色
        self.root.configure(bg="#f0f8ff")

        # 线程相关变量
        self.brute_thread = None
        self.brute_worker = None

        # 创建自定义样式
        self.setup_styles()

        # 创建标签页
        self.tab_control = ttk.Notebook(root, style="Custom.TNotebook")
        self.tab_encrypt = ttk.Frame(self.tab_control, style="Custom.TFrame")  # 加密页面
        self.tab_decrypt = ttk.Frame(self.tab_control, style="Custom.TFrame")  # 解密页面
        self.tab_str = ttk.Frame(self.tab_control, style="Custom.TFrame")  # 字符串加密
        self.tab_brute = ttk.Frame(self.tab_control, style="Custom.TFrame")  # 暴力破解
        self.tab_collision = ttk.Frame(self.tab_control, style="Custom.TFrame")  # 密钥碰撞分析

        self.tab_control.add(self.tab_encrypt, text="基本加密")
        self.tab_control.add(self.tab_decrypt, text="基本解密")
        self.tab_control.add(self.tab_str, text="字符串加密")
        self.tab_control.add(self.tab_brute, text="暴力破解")
        self.tab_control.add(self.tab_collision, text="密钥碰撞分析")
        self.tab_control.pack(expand=1, fill="both", padx=10, pady=10)

        self.init_tab_encrypt()
        self.init_tab_decrypt()
        self.init_tab_str()
        self.init_tab_brute()
        self.init_tab_collision()

    def setup_styles(self):
        """设置自定义样式"""
        self.style = ttk.Style()

        # 配置主题
        self.style.theme_use('clam')

        # 配置标签页样式
        self.style.configure("Custom.TNotebook", background="#e6f2ff", borderwidth=0)
        self.style.configure("Custom.TNotebook.Tab",
                             font=("微软雅黑", 10, "bold"),
                             padding=[15, 5],
                             background="#cce5ff",
                             foreground="#2c3e50")
        self.style.map("Custom.TNotebook.Tab",
                       background=[("selected", "#4a90e2"), ("active", "#6ba8e9")],
                       foreground=[("selected", "white")])

        # 配置框架样式
        self.style.configure("Custom.TFrame", background="#f0f8ff")

        # 配置标签样式
        self.style.configure("Title.TLabel",
                             font=("微软雅黑", 11, "bold"),
                             background="#f0f8ff",
                             foreground="#2c3e50",
                             padding=5)
        self.style.configure("Subtitle.TLabel",
                             font=("微软雅黑", 10),
                             background="#f0f8ff",
                             foreground="#34495e",
                             padding=3)

        # 配置按钮样式
        self.style.configure("Accent.TButton",
                             font=("微软雅黑", 10, "bold"),
                             background="#4a90e2",
                             foreground="white",
                             borderwidth=0,
                             focuscolor="none",
                             padding=(15, 8))
        self.style.map("Accent.TButton",
                       background=[("active", "#3a7bd5"), ("pressed", "#2a5ba5")])

        self.style.configure("Secondary.TButton",
                             font=("微软雅黑", 9),
                             background="#87ceeb",
                             foreground="#2c3e50",
                             borderwidth=0,
                             focuscolor="none",
                             padding=(12, 6))
        self.style.map("Secondary.TButton",
                       background=[("active", "#6cb2d6"), ("pressed", "#4a90c2")])

        # 配置输入框样式
        self.style.configure("Custom.TEntry",
                             fieldbackground="white",
                             borderwidth=2,
                             relief="solid",
                             padding=5)
        self.style.map("Custom.TEntry",
                       bordercolor=[("focus", "#4a90e2")])

        # 配置进度条样式
        self.style.configure("Custom.Horizontal.TProgressbar",
                             thickness=20,
                             background="#4a90e2",
                             troughcolor="#e6f2ff",
                             borderwidth=0,
                             lightcolor="#6ba8e9",
                             darkcolor="#3a7bd5")

    def create_section(self, parent, title, row):
        """创建带标题的区域"""
        frame = ttk.Frame(parent, style="Custom.TFrame")
        frame.grid(row=row, column=0, columnspan=2, sticky="we", padx=10, pady=5)

        title_label = ttk.Label(frame, text=title, style="Title.TLabel")
        title_label.pack(anchor="w")

        # 添加分隔线
        separator = ttk.Separator(frame, orient="horizontal")
        separator.pack(fill="x", pady=(0, 10))

        return frame

    def init_tab_encrypt(self):
        """加密页面"""
        # 标题
        title_frame = self.create_section(self.tab_encrypt, "基本加密", 0)

        # 输入区域
        input_frame = ttk.Frame(self.tab_encrypt, style="Custom.TFrame")
        input_frame.grid(row=1, column=0, columnspan=2, sticky="we", padx=20, pady=10)

        ttk.Label(input_frame, text="8位明文 (0-1组成，如10101010):", style="Subtitle.TLabel").grid(row=0, column=0,
                                                                                                   padx=10, pady=10,
                                                                                                   sticky=tk.W)
        self.encrypt_plain_entry = ttk.Entry(input_frame, width=30, style="Custom.TEntry", font=("Consolas", 10))
        self.encrypt_plain_entry.grid(row=0, column=1, padx=10, pady=10)
        self.encrypt_plain_entry.insert(0, "10101010")  # 默认值

        ttk.Label(input_frame, text="10位密钥 (0-1组成，如1010101010):", style="Subtitle.TLabel").grid(row=1, column=0,
                                                                                                      padx=10, pady=10,
                                                                                                      sticky=tk.W)
        self.encrypt_key_entry = ttk.Entry(input_frame, width=30, style="Custom.TEntry", font=("Consolas", 10))
        self.encrypt_key_entry.grid(row=1, column=1, padx=10, pady=10)
        self.encrypt_key_entry.insert(0, "1010101010")  # 默认值

        # 结果区域
        result_frame = ttk.Frame(self.tab_encrypt, style="Custom.TFrame")
        result_frame.grid(row=2, column=0, columnspan=2, sticky="we", padx=20, pady=10)

        ttk.Label(result_frame, text="加密结果:", style="Subtitle.TLabel").grid(row=0, column=0, padx=10, pady=10,
                                                                                sticky=tk.W)
        self.encrypt_result_entry = ttk.Entry(result_frame, width=30, style="Custom.TEntry", font=("Consolas", 10),
                                              state="readonly")
        self.encrypt_result_entry.grid(row=0, column=1, padx=10, pady=10)

        # 按钮区域
        button_frame = ttk.Frame(self.tab_encrypt, style="Custom.TFrame")
        button_frame.grid(row=3, column=0, columnspan=2, pady=20)
        ttk.Button(button_frame, text="执行加密", command=self.encrypt_bit, style="Accent.TButton").pack(pady=10)

    def init_tab_decrypt(self):
        """解密页面"""
        # 标题
        title_frame = self.create_section(self.tab_decrypt, "基本解密", 0)

        # 输入区域
        input_frame = ttk.Frame(self.tab_decrypt, style="Custom.TFrame")
        input_frame.grid(row=1, column=0, columnspan=2, sticky="we", padx=20, pady=10)

        ttk.Label(input_frame, text="8位密文 (0-1组成，如10101010):", style="Subtitle.TLabel").grid(row=0, column=0,
                                                                                                   padx=10, pady=10,
                                                                                                   sticky=tk.W)
        self.decrypt_cipher_entry = ttk.Entry(input_frame, width=30, style="Custom.TEntry", font=("Consolas", 10))
        self.decrypt_cipher_entry.grid(row=0, column=1, padx=10, pady=10)

        ttk.Label(input_frame, text="10位密钥 (0-1组成，如1010101010):", style="Subtitle.TLabel").grid(row=1, column=0,
                                                                                                      padx=10, pady=10,
                                                                                                      sticky=tk.W)
        self.decrypt_key_entry = ttk.Entry(input_frame, width=30, style="Custom.TEntry", font=("Consolas", 10))
        self.decrypt_key_entry.grid(row=1, column=1, padx=10, pady=10)

        # 结果区域
        result_frame = ttk.Frame(self.tab_decrypt, style="Custom.TFrame")
        result_frame.grid(row=2, column=0, columnspan=2, sticky="we", padx=20, pady=10)

        ttk.Label(result_frame, text="解密结果:", style="Subtitle.TLabel").grid(row=0, column=0, padx=10, pady=10,
                                                                                sticky=tk.W)
        self.decrypt_result_entry = ttk.Entry(result_frame, width=30, style="Custom.TEntry", font=("Consolas", 10),
                                              state="readonly")
        self.decrypt_result_entry.grid(row=0, column=1, padx=10, pady=10)

        # 按钮区域
        button_frame = ttk.Frame(self.tab_decrypt, style="Custom.TFrame")
        button_frame.grid(row=3, column=0, columnspan=2, pady=20)
        ttk.Button(button_frame, text="执行解密", command=self.decrypt_bit, style="Accent.TButton").pack(pady=10)

    def encrypt_bit(self):
        """加密8位数据"""
        try:
            plaintext = self.encrypt_plain_entry.get().strip()
            key = self.encrypt_key_entry.get().strip()
            if len(plaintext) != 8 or not all(c in "01" for c in plaintext):
                messagebox.showerror("错误", "明文必须是8位0-1字符串")
                return
            if len(key) != 10 or not all(c in "01" for c in key):
                messagebox.showerror("错误", "密钥必须是10位0-1字符串")
                return
            plain_bits = [int(c) for c in plaintext]
            key_bits = [int(c) for c in key]
            cipher_bits = sdes_encrypt(plain_bits, key_bits)
            ciphertext = "".join(map(str, cipher_bits))
            self.encrypt_result_entry.config(state="normal")
            self.encrypt_result_entry.delete(0, tk.END)
            self.encrypt_result_entry.insert(0, ciphertext)
            self.encrypt_result_entry.config(state="readonly")
        except Exception as e:
            messagebox.showerror("错误", str(e))

    def decrypt_bit(self):
        """解密8位数据"""
        try:
            ciphertext = self.decrypt_cipher_entry.get().strip()
            key = self.decrypt_key_entry.get().strip()
            if len(ciphertext) != 8 or not all(c in "01" for c in ciphertext):
                messagebox.showerror("错误", "密文必须是8位0-1字符串")
                return
            if len(key) != 10 or not all(c in "01" for c in key):
                messagebox.showerror("错误", "密钥必须是10位0-1字符串")
                return
            cipher_bits = [int(c) for c in ciphertext]
            key_bits = [int(c) for c in key]
            plain_bits = sdes_decrypt(cipher_bits, key_bits)
            plaintext = "".join(map(str, plain_bits))
            self.decrypt_result_entry.config(state="normal")
            self.decrypt_result_entry.delete(0, tk.END)
            self.decrypt_result_entry.insert(0, plaintext)
            self.decrypt_result_entry.config(state="readonly")
        except Exception as e:
            messagebox.showerror("错误", str(e))

    def init_tab_str(self):
        """字符串加密页面"""
        # 标题
        title_frame = self.create_section(self.tab_str, "字符串加密解密", 0)

        # 输入区域
        input_frame = ttk.Frame(self.tab_str, style="Custom.TFrame")
        input_frame.grid(row=1, column=0, columnspan=2, sticky="we", padx=20, pady=10)

        ttk.Label(input_frame, text="输入字符串 (将按1字节分组加密/解密):", style="Subtitle.TLabel").grid(row=0, column=0,
                                                                                                     padx=10, pady=10,
                                                                                                     sticky=tk.NW)
        self.str_input = tk.Text(input_frame, width=30, height=5, font=("微软雅黑", 9),
                                 bg="white", relief="solid", bd=1, padx=5, pady=5)
        self.str_input.grid(row=0, column=1, padx=10, pady=10)

        ttk.Label(input_frame, text="10位密钥 (0-1组成):", style="Subtitle.TLabel").grid(row=1, column=0, padx=10,
                                                                                         pady=10, sticky=tk.W)
        self.str_key_entry = ttk.Entry(input_frame, width=30, style="Custom.TEntry", font=("Consolas", 10))
        self.str_key_entry.grid(row=1, column=1, padx=10, pady=10)
        self.str_key_entry.insert(0, "1010101010")  # 默认值

        # 结果区域
        result_frame = ttk.Frame(self.tab_str, style="Custom.TFrame")
        result_frame.grid(row=2, column=0, columnspan=2, sticky="we", padx=20, pady=10)

        ttk.Label(result_frame, text="加密/解密结果:", style="Subtitle.TLabel").grid(row=0, column=0, padx=10, pady=10,
                                                                                     sticky=tk.NW)
        self.str_result = tk.Text(result_frame, width=30, height=5, state="disabled", font=("微软雅黑", 9),
                                  bg="#f8f9fa", relief="solid", bd=1, padx=5, pady=5)
        self.str_result.grid(row=0, column=1, padx=10, pady=10)

        # 状态信息显示
        status_frame = ttk.Frame(self.tab_str, style="Custom.TFrame")
        status_frame.grid(row=3, column=0, columnspan=2, sticky="we", padx=20, pady=5)

        ttk.Label(status_frame, text="状态信息:", style="Subtitle.TLabel").grid(row=0, column=0, padx=10, pady=5,
                                                                                sticky=tk.W)
        self.str_status = ttk.Label(status_frame, text="就绪", style="Subtitle.TLabel")
        self.str_status.grid(row=0, column=1, padx=10, pady=5, sticky=tk.W)

        # 按钮区域
        btn_frame = ttk.Frame(self.tab_str, style="Custom.TFrame")
        btn_frame.grid(row=4, column=0, columnspan=2, pady=10)
        ttk.Button(btn_frame, text="字符串加密", command=self.encrypt_str, style="Accent.TButton").pack(side=tk.LEFT,
                                                                                                        padx=20)
        ttk.Button(btn_frame, text="字符串解密", command=self.decrypt_str, style="Secondary.TButton").pack(side=tk.LEFT,
                                                                                                           padx=20)

    def encrypt_str(self):
        """加密ASCII字符串（带填充和校验和）"""
        try:
            s = self.str_input.get("1.0", tk.END).strip()
            key = self.str_key_entry.get().strip()

            if len(key) != 10 or not all(c in "01" for c in key):
                messagebox.showerror("错误", "密钥必须是10位0-1字符串")
                return

            # 将字符串转换为字节数据
            data_bytes = s.encode('latin-1')  # 使用latin-1编码确保所有字节都能表示

            # 计算校验和并添加到数据末尾
            checksum = calculate_checksum(data_bytes)
            data_with_checksum = data_bytes + checksum

            # PKCS#7填充
            padded_data = pkcs7_pad(data_with_checksum)

            # 加密
            key_bits = [int(c) for c in key]
            encrypted_bytes = []

            for byte in padded_data:
                # 将每个字节转换为8位二进制
                plain_bits = [int(bit) for bit in f"{byte:08b}"]
                # 加密
                cipher_bits = sdes_encrypt(plain_bits, key_bits)
                # 将加密后的二进制转换回字节
                cipher_byte = int("".join(map(str, cipher_bits)), 2)
                encrypted_bytes.append(cipher_byte)

            # 将加密后的字节转换为字符串（可能是乱码）
            cipher_str = bytes(encrypted_bytes).decode('latin-1')

            # 显示结果
            self.str_result.config(state="normal")
            self.str_result.delete("1.0", tk.END)
            self.str_result.insert("1.0", cipher_str)
            self.str_result.config(state="disabled")

            # 更新状态
            self.str_status.config(text=f"加密成功")
            self.str_status.configure(foreground="#27ae60")

        except Exception as e:
            self.str_status.config(text=f"加密失败: {str(e)}")
            self.str_status.configure(foreground="#e74c3c")
            messagebox.showerror("错误", str(e))

    def decrypt_str(self):
        """解密ASCII字符串（带去填充和校验）"""
        try:
            cipher_str = self.str_input.get("1.0", tk.END).strip()
            key = self.str_key_entry.get().strip()

            if len(key) != 10 or not all(c in "01" for c in key):
                messagebox.showerror("错误", "密钥必须是10位0-1字符串")
                return

            # 将密文字符串转换为字节数据
            cipher_bytes = cipher_str.encode('latin-1')

            # 解密
            key_bits = [int(c) for c in key]
            decrypted_bytes = []

            for byte in cipher_bytes:
                # 将每个字节转换为8位二进制
                cipher_bits = [int(bit) for bit in f"{byte:08b}"]
                # 解密
                plain_bits = sdes_decrypt(cipher_bits, key_bits)
                # 将解密后的二进制转换回字节
                plain_byte = int("".join(map(str, plain_bits)), 2)
                decrypted_bytes.append(plain_byte)

            # 将解密后的字节数据转换为bytes对象
            decrypted_data = bytes(decrypted_bytes)

            # 去填充
            try:
                data_with_checksum = pkcs7_unpad(decrypted_data)
            except ValueError as e:
                raise ValueError(f"填充验证失败: {str(e)}")

            # 验证校验和
            if len(data_with_checksum) < 1:
                raise ValueError("数据太短，无法包含校验和")

            received_checksum = data_with_checksum[-1:]
            data_bytes = data_with_checksum[:-1]
            calculated_checksum = calculate_checksum(data_bytes)

            if received_checksum != calculated_checksum:
                raise ValueError("校验和不匹配，数据可能已被篡改")

            # 转换为字符串
            plain_str = data_bytes.decode('latin-1')

            # 显示结果
            self.str_result.config(state="normal")
            self.str_result.delete("1.0", tk.END)
            self.str_result.insert("1.0", plain_str)
            self.str_result.config(state="disabled")

            # 更新状态
            self.str_status.config(text=f"解密成功: 校验和验证通过")
            self.str_status.configure(foreground="#27ae60")

        except Exception as e:
            self.str_status.config(text=f"解密失败: {str(e)}")
            self.str_status.configure(foreground="#e74c3c")
            messagebox.showerror("错误", str(e))

    def init_tab_brute(self):
        """暴力破解页面（带中断功能）"""
        # 标题
        title_frame = self.create_section(self.tab_brute, "暴力破解分析", 0)

        # 输入区域
        input_frame = ttk.Frame(self.tab_brute, style="Custom.TFrame")
        input_frame.grid(row=1, column=0, columnspan=2, sticky="we", padx=20, pady=10)

        ttk.Label(input_frame, text="已知明文 (8位0-1):", style="Subtitle.TLabel").grid(row=0, column=0, padx=10,
                                                                                        pady=10, sticky=tk.W)
        self.brute_plain = ttk.Entry(input_frame, width=30, style="Custom.TEntry", font=("Consolas", 10))
        self.brute_plain.grid(row=0, column=1, padx=10, pady=10)
        self.brute_plain.insert(0, "10101010")  # 默认值

        ttk.Label(input_frame, text="对应密文 (8位0-1):", style="Subtitle.TLabel").grid(row=1, column=0, padx=10,
                                                                                        pady=10, sticky=tk.W)
        self.brute_cipher = ttk.Entry(input_frame, width=30, style="Custom.TEntry", font=("Consolas", 10))
        self.brute_cipher.grid(row=1, column=1, padx=10, pady=10)

        # 进度区域
        progress_frame = ttk.Frame(self.tab_brute, style="Custom.TFrame")
        progress_frame.grid(row=2, column=0, columnspan=2, sticky="we", padx=20, pady=10)

        ttk.Label(progress_frame, text="破解进度:", style="Subtitle.TLabel").grid(row=0, column=0, padx=10, pady=10,
                                                                                  sticky=tk.W)
        self.progress = ttk.Progressbar(progress_frame, orient="horizontal", length=200, mode="determinate",
                                        style="Custom.Horizontal.TProgressbar")
        self.progress.grid(row=0, column=1, padx=10, pady=10)

        # 结果区域
        result_frame = ttk.Frame(self.tab_brute, style="Custom.TFrame")
        result_frame.grid(row=3, column=0, columnspan=2, sticky="we", padx=20, pady=10)

        ttk.Label(result_frame, text="破解结果:", style="Subtitle.TLabel").grid(row=0, column=0, padx=10, pady=10,
                                                                                sticky=tk.NW)
        self.brute_result = tk.Text(result_frame, width=40, height=5, state="disabled", font=("Consolas", 9),
                                    bg="#f8f9fa", relief="solid", bd=1, padx=5, pady=5)
        self.brute_result.grid(row=0, column=1, padx=10, pady=10)

        # 按钮框架
        btn_frame = ttk.Frame(self.tab_brute, style="Custom.TFrame")
        btn_frame.grid(row=4, column=0, columnspan=2, pady=10)
        self.start_brute_btn = ttk.Button(btn_frame, text="开始暴力破解", command=self.start_brute,
                                          style="Accent.TButton")
        self.start_brute_btn.pack(side=tk.LEFT, padx=20)
        self.stop_brute_btn = ttk.Button(btn_frame, text="停止破解", command=self.stop_brute, style="Secondary.TButton",
                                         state="disabled")
        self.stop_brute_btn.pack(side=tk.LEFT, padx=20)

    def update_progress(self, value):
        """更新进度条（线程安全）"""
        if self.root.winfo_exists():
            self.progress["value"] = value
            self.root.update_idletasks()

    def start_brute(self):
        """启动暴力破解（多线程）"""
        try:
            plaintext = self.brute_plain.get().strip()
            ciphertext = self.brute_cipher.get().strip()

            if len(plaintext) != 8 or not all(c in "01" for c in plaintext):
                messagebox.showerror("错误", "明文必须是8位0-1字符串")
                return
            if len(ciphertext) != 8 or not all(c in "01" for c in ciphertext):
                messagebox.showerror("错误", "密文必须是8位0-1字符串")
                return

            plain_bits = [int(c) for c in plaintext]
            cipher_bits = [int(c) for c in ciphertext]

            # 禁用开始按钮，启用停止按钮
            self.start_brute_btn.config(state="disabled")
            self.stop_brute_btn.config(state="normal")
            self.progress["value"] = 0
            self.brute_result.config(state="normal")
            self.brute_result.delete("1.0", tk.END)
            self.brute_result.insert("1.0", "正在破解中...\n")
            self.brute_result.config(state="disabled")

            # 创建破解实例和线程
            self.brute_worker = BruteForce(plain_bits, cipher_bits, self.update_progress)
            self.brute_thread = threading.Thread(target=self.run_brute, daemon=True)
            self.brute_thread.start()

        except Exception as e:
            messagebox.showerror("错误", str(e))

    def stop_brute(self):
        """停止暴力破解"""
        if self.brute_worker and self.brute_thread and self.brute_thread.is_alive():
            self.brute_worker.stop()
            self.brute_result.config(state="normal")
            self.brute_result.insert(tk.END, "正在停止破解...\n")
            self.brute_result.config(state="disabled")

    def run_brute(self):
        """执行破解并显示结果"""
        self.brute_worker.run()
        result = self.brute_worker.get_result()

        # 在主线程中更新UI
        def update_ui():
            self.progress["value"] = 100 if result["completed"] else self.progress["value"]
            self.brute_result.config(state="normal")
            self.brute_result.delete("1.0", tk.END)

            if result["completed"]:
                self.brute_result.insert("1.0", f"破解完成，找到{result['count']}个密钥:\n")
            else:
                self.brute_result.insert("1.0", f"破解已停止，已找到{result['count']}个密钥:\n")

            # 显示所有找到的密钥
            for i, key in enumerate(result["keys"]):
                self.brute_result.insert(tk.END, f"密钥 #{i + 1}: {key:010b}\n")

            self.brute_result.insert(tk.END, f"耗时: {result['time']}秒")
            self.brute_result.config(state="disabled")

            # 恢复按钮状态
            self.start_brute_btn.config(state="normal")
            self.stop_brute_btn.config(state="disabled")

        self.root.after(0, update_ui)

    def init_tab_collision(self):
        """密钥碰撞分析页面"""
        # 标题
        title_frame = self.create_section(self.tab_collision, "密钥碰撞分析", 0)

        # 输入区域
        input_frame = ttk.Frame(self.tab_collision, style="Custom.TFrame")
        input_frame.grid(row=1, column=0, columnspan=2, sticky="we", padx=20, pady=10)

        ttk.Label(input_frame, text="随机明文分组 (8位0-1，留空则随机):", style="Subtitle.TLabel").grid(row=0, column=0,
                                                                                                       padx=10, pady=10,
                                                                                                       sticky=tk.W)
        self.collision_plain = ttk.Entry(input_frame, width=30, style="Custom.TEntry", font=("Consolas", 10))
        self.collision_plain.grid(row=0, column=1, padx=10, pady=10)

        # 按钮区域
        button_frame = ttk.Frame(self.tab_collision, style="Custom.TFrame")
        button_frame.grid(row=2, column=0, columnspan=2, pady=10)
        ttk.Button(button_frame, text="分析密钥碰撞", command=self.analyze_collision, style="Accent.TButton").pack(
            pady=10)

        # 结果区域
        result_frame = ttk.Frame(self.tab_collision, style="Custom.TFrame")
        result_frame.grid(row=3, column=0, columnspan=2, sticky="we", padx=20, pady=10)

        ttk.Label(result_frame, text="分析结果:", style="Subtitle.TLabel").grid(row=0, column=0, padx=10, pady=10,
                                                                                sticky=tk.NW)
        self.collision_result = tk.Text(result_frame, width=50, height=10, state="disabled", font=("微软雅黑", 9),
                                        bg="#f8f9fa", relief="solid", bd=1, padx=5, pady=5)
        self.collision_result.grid(row=0, column=1, padx=10, pady=10)

    def analyze_collision(self):
        """分析密钥碰撞"""
        try:
            plain_input = self.collision_plain.get().strip()
            if plain_input:
                if len(plain_input) != 8 or not all(c in "01" for c in plain_input):
                    messagebox.showerror("错误", "明文必须是8位0-1字符串")
                    return
                plain_bits = [int(c) for c in plain_input]
            else:
                plain_bits = [int(bit) for bit in bin(random.getrandbits(8))[2:].zfill(8)]
                plain_str = "".join(map(str, plain_bits))
                self.collision_plain.delete(0, tk.END)
                self.collision_plain.insert(0, plain_str)

            cipher_map = {}
            for i in range(1024):
                key = int_to_bits(i, 10)
                cipher = bits_to_int(sdes_encrypt(plain_bits, key))
                if cipher not in cipher_map:
                    cipher_map[cipher] = []
                cipher_map[cipher].append(i)

            collision_ciphers = {c: keys for c, keys in cipher_map.items() if len(keys) > 1}

            self.collision_result.config(state="normal")
            self.collision_result.delete("1.0", tk.END)
            self.collision_result.insert("1.0", f"明文: {''.join(map(str, plain_bits))}\n\n")
            self.collision_result.insert(tk.END, f"总密钥数: 1024\n")
            self.collision_result.insert(tk.END, f"存在碰撞的密文数: {len(collision_ciphers)}\n\n")
            if collision_ciphers:
                self.collision_result.insert(tk.END, "示例碰撞（同一密文对应多个密钥）:\n")
                first_cipher, keys = next(iter(collision_ciphers.items()))
                self.collision_result.insert(tk.END, f"密文: {first_cipher:08b}\n")
                self.collision_result.insert(tk.END, f"对应密钥（10位）: {[f'{k:010b}' for k in keys[:5]]}\n")
                if len(keys) > 5:
                    self.collision_result.insert(tk.END, f"... 共{len(keys)}个密钥")
            else:
                self.collision_result.insert(tk.END, "未发现碰撞（概率极低）")
            self.collision_result.config(state="disabled")
        except Exception as e:
            messagebox.showerror("错误", str(e))


if __name__ == "__main__":
    root = tk.Tk()
    app = SDesGUI(root)
    root.mainloop()
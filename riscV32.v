//Program Counter
module Program_counter(clk,reset,PC_in,PC_out);
    input             clk, reset;             // Clock and reset inputs
    input      [31:0] PC_in;           // 32-bit input for the next program counter value
    output reg [31:0] PC_out;     // 32-bit output for the current program counter value
    
    always @(posedge clk or posedge reset) // Trigger on clock or reset
    begin
        if (reset)                   // If reset is high, set PC_out to 0
            PC_out <= 32'b00;        // 32-bit zero value (binary)
        else                         // Else update PC_out with PC_in
            PC_out <= PC_in;
    end
endmodule

//PC + 4 (32 bits)
module PCplus4(fromPC, nextPC);
    input  [31:0] fromPC;        // 32-bit input: current Program Counter value
    output [31:0] nextPC;       // 32-bit output: next Program Counter value
    
    assign nextPC = 4 + fromPC; // Increment PC by 4 to get the next instruction's address
endmodule

//Instruction memory
/*module instruction_mem(clk, reset, read_address, instruction_out);
    input             clk, reset;          // Clock and reset signals
    input      [31:0] read_address;        // 32-bit read address input
    output reg [31:0] instruction_out;     // 32-bit instruction output
    
    reg [31:0] I_Mem[63:0];                // Memory array: 64 instructions, 32 bits each
    integer k,i;                             // Variable for the loop during reset
    
    always @(posedge clk or posedge reset) // Trigger on clock or reset
    begin
	
        if (reset)                         // If reset is high, clear the memory
        begin
            for (k = 0; k < 64; k = k + 1) // Initialize memory to zero
                I_Mem[k] = 32'b00;
        end
        else                               // Else, read the instruction at read_address
            //instruction_out <= I_Mem[read_address[31:1]];
			//R type
			I_Mem[0]  = 32'b00000000000000000000000000000000;
			I_Mem[4]  = 32'b0000000_11001_10000_000_01101_0110011; //ADD x13, x16, x25
			I_Mem[8]  = 32'b0100000_00011_01000_000_00101_0110011; //
			I_Mem[12] = 32'b0000000_00101_00011_110_00100_0110011;
			
			I_Mem[16] = 32'b000000000101_00011_000_00101_0010011;  // ADDI x5, x3, 10
			I_Mem[20] = 32'b000000000100_00010_010_00100_0000011;  // LW x4, 8(x2)
			I_Mem[24] = 32'b0000000_00101_00011_010_00110_0100011;  // SW x5, 12(x3)
			I_Mem[28] = 32'b1111111_00101_00100_000_11110_1100011;  // BEQ x4, x5, -4	
			
		end
	always @(posedge clk)
	begin
		for (i=0;i<64;i=i+1)
			instruction_out <= I_Mem[i];
	end
		
	
	
endmodule */

module instruction_mem(clk, reset, read_address, instruction_out);
    input             clk, reset;          // Clock and reset signals
    input      [31:0] read_address;        // 32-bit read address input
    output reg [31:0] instruction_out;     // 32-bit instruction output
    
    reg [31:0] I_Mem[63:0];                // Memory array: 64 instructions, 32 bits each
    integer k;                             // Variable for the loop during reset

    // Preload instructions during initialization
    initial begin
        // Load the instruction memory with some example instructions
        I_Mem[0]  = 32'b00000000000000000000000000000000;  // NOP
        I_Mem[4]  = 32'b0000000_11001_10000_000_01101_0110011; // ADD x13, x16, x25
        I_Mem[8]  = 32'b0100000_00011_01000_000_00101_0110011; // SUB
        I_Mem[12]  = 32'b0000000_00101_00011_110_00100_0110011; // XOR
        
        I_Mem[16]  = 32'b000000000101_00011_000_00101_0010011;  // ADDI x5, x3, 10
        I_Mem[20]  = 32'b000000000100_00010_010_00100_0000011;  // LW x4, 8(x2)
        I_Mem[24]  = 32'b0000000_00101_00011_010_00110_0100011;  // SW x5, 12(x3)
        I_Mem[28]  = 32'b1111111_00101_00100_000_11110_1100011;  // BEQ x4, x5, -4
    end

    always @(posedge clk)
    begin
        if (!reset)  // Only fetch instruction when reset is low
        begin
            instruction_out <= I_Mem[read_address[31:0]];  // Fetch word-aligned instruction
        end
    end
endmodule



//Register file
module Reg_file(clk,reset,RegWrite,Rs1,Rs2,Rd,Write_data,Read_data1,Read_data2);
    input         clk, reset, RegWrite;            // Clock, reset, and write enable signals
    input  [4:0]  Rs1, Rs2, Rd;               // 5-bit register addresses (32 registers)
    input  [31:0] Write_data;                // 32-bit data to be written
    output [31:0] Read_data1, Read_data2;   // 32-bit data outputs
    
    reg [31:0] Registers [31:0];            // 32 registers, each 32 bits wide
	
	initial begin
	
	Registers[0] = 0;
	Registers[1] = 45;
	Registers[2] = 12;
	Registers[3] = 23;
	Registers[4] = 87;
	Registers[5] = 35;
	Registers[6] = 56;
	Registers[7] = 94;
	Registers[8] = 23;
	Registers[9] = 11;
	Registers[10] = 67;
	Registers[11] = 45;
	Registers[12] = 89;
	Registers[13] = 57;
	Registers[14] = 22;
	Registers[15] = 43;
	Registers[16] = 98;
	Registers[17] = 31;
	Registers[18] = 12;
	Registers[19] = 74;
	Registers[20] = 80;
	Registers[21] = 40;
	Registers[22] = 56;
	Registers[23] = 21;
	Registers[24] = 78;
	Registers[25] = 12;
	Registers[26] = 31;
	Registers[27] = 67;
	Registers[28] = 90;
	Registers[29] = 40;
	Registers[30] = 89;
	Registers[31] = 67;

	end
	
    integer k;                              // Loop index for reset initialization
    
    always @(posedge clk or posedge reset)  // Triggered by clock or reset
    begin
        if (reset) begin                    // If reset is high, clear all registers
            for (k = 0; k < 32; k = k + 1) 
                Registers[k] <= 32'b00;
        end
        else if (RegWrite) begin            // If write is enabled, write data to the register
            Registers[Rd] <= Write_data;
        end
    end
    
    // Read values from registers addressed by Rs1 and Rs2
    assign Read_data1 = Registers[Rs1];      // Read from Rs1 register
    assign Read_data2 = Registers[Rs2];      // Read from Rs2 register
endmodule

//Immediate generator
module ImmGen(opcode, instruction, ImmExt);
    input      [6:0]  opcode;                     // 7-bit opcode to identify instruction type
    input      [31:0] instruction;               // 32-bit instruction input
    output reg [31:0] ImmExt;               // 32-bit sign-extended immediate output
    
    always @(*)                             // Combinational logic block (runs continuously)
    begin
        case (opcode)                       // Opcode decides the type of immediate format
            7'b0000011: ImmExt <= {{20{instruction[31]}}, instruction[31:20]};  // I-type immediate
            7'b0100011: ImmExt <= {{20{instruction[31]}}, instruction[31:25], instruction[11:7]};  // S-type immediate
            7'b1100011: ImmExt <= {{19{instruction[31]}}, instruction[31], instruction[30:25], instruction[11:8], 1'b0};  // B-type immediate
        endcase
    end
endmodule

//Control unit
module Control_unit(instruction, Branch, Memread, MemtoReg, ALUOp, MemWrite, ALUSrc, RegWrite);
    input       [6:0] instruction;  // 7-bit opcode part of the instruction
    output reg        Branch, Memread, MemtoReg, MemWrite, ALUSrc, RegWrite;  // Control signalsBranch, Memread, MemtoReg, MemWrite, ALUSrc, RegWrite;  // Control signals
    output reg  [1:0] ALUOp;  // ALU operation control signal (2 bits)
    
    always @(*)  // Combinational logic block
    begin
        case (instruction)  // Based on opcode, control signals are set
            7'b0110011 : {ALUSrc, MemtoReg, RegWrite, Memread, MemWrite, Branch, ALUOp} <= 8'b00100010;  // R-type
            7'b0000011 : {ALUSrc, MemtoReg, RegWrite, Memread, MemWrite, Branch, ALUOp} <= 8'b11110000;  // I-type (load)
            7'b0100011 : {ALUSrc, MemtoReg, RegWrite, Memread, MemWrite, Branch, ALUOp} <= 8'b10001000;  // S-type (store)
            7'b1100011 : {ALUSrc, MemtoReg, RegWrite, Memread, MemWrite, Branch, ALUOp} <= 8'b00000101;  // B-type (branch)
        endcase
    end
endmodule

// ALU Unit Module
module ALU_unit(A, B, Control_in, ALU_Result, zero);

    // Inputs: Two 32-bit operands A and B, and a 4-bit control signal
    input [31:0] A, B;
    input [3:0] Control_in;

    // Outputs: 32-bit result of the ALU operation, and a zero flag
    output reg [31:0] ALU_Result;
    output reg zero;

    // Always block: executes whenever A, B, or Control_in change
    always @(*)
    begin
        // Case statement based on the ALU control input
		case(Control_in)
        4'b0000: begin zero <= 0; ALU_Result <= A & B; end  // AND operation
		4'b0001: begin zero <= 0; ALU_Result <= A | B; end  // OR operation
		4'b0010: begin zero <= 0; ALU_Result <= A + B; end  // ADD operation
		4'b0110: begin if (A == B) zero <= 1; else zero <= 0; ALU_Result <= A - B; end  // SUB operation with zero flag
        endcase
    end

endmodule


// ALU Control Module
module ALU_Control(ALUOp, fun7, fun3, Control_out);
    // Inputs: ALUOp (2 bits), fun7 (1 bit), fun3 (3 bits)
    input       fun7;  // This is a signal from the instruction that helps determine the operation
    input [2:0] fun3;  // Another signal from the instruction that specifies the operation
    input [1:0] ALUOp;  // 2-bit ALU operation code (from the control unit)

    // Output: 4-bit control signal to instruct the ALU which operation to perform
    output reg [3:0] Control_out;

    // Always block: executes whenever any input changes
    always @(*)
    begin
        // Case statement based on concatenation of ALUOp, fun7, and fun3
        case({ALUOp, fun7, fun3})
            6'b00_0_000 : Control_out <= 4'b0010;  // Load/Store (ADD operation)
            6'b01_0_000 : Control_out <= 4'b0110;  // Branch (SUB operation)
            6'b10_0_000 : Control_out <= 4'b0010;  // R-type (ADD)
            6'b10_1_000 : Control_out <= 4'b0110;  // R-type (SUB)
            6'b10_0_111 : Control_out <= 4'b0000;  // R-type (AND)
            6'b10_0_110 : Control_out <= 4'b0001;  // R-type (OR)
        endcase
    end
endmodule

// Data Memory Module
module Data_Memory(clk, reset, MemWrite, Memread, read_address, Write_data, MemData_out);

    input         clk, reset;                   // Clock and reset inputs
    input         MemWrite, Memread;            // Control signals for memory write and memory read
    input  [31:0] read_address;          // Address to read/write from/to memory
    input  [31:0] Write_data;            // Data to write to memory during a write operation
    output [31:0] MemData_out;          // Data output during a read operation
    
    integer k;                          // Integer used for the reset loop
    reg [31:0] D_Memory[63:0];          // Memory array with 64 32-bit locations
    
    // Always block: handles memory write and reset
    always @(posedge clk or posedge reset)
    begin
        if (reset)
        begin
            // Reset memory contents to 0
            for (k = 0; k < 64; k = k + 1)
                D_Memory[k] <= 32'b00;
        end
        else if (MemWrite)
        begin
            // Write data to memory when MemWrite is enabled
            D_Memory[read_address] <= Write_data;
        end
    end

    // Assign data output: Reads data from memory when Memread is enabled, otherwise outputs 0
    assign MemData_out = (Memread) ? D_Memory[read_address] : 32'b00;

endmodule

//Multiplexer
module Mux1(sel1,A1,B1,Mux1_out);
	input         sel1;
	input  [31:0] A1,B1;
	output [31:0] Mux1_out;
	
	assign Mux1_out = (sel1==1'b0) ? A1:B1;
endmodule

module Mux2(sel2,A2,B2,Mux2_out);
	input         sel2;
	input  [31:0] A2,B2;
	output [31:0] Mux2_out;
	
	assign Mux2_out = (sel2==1'b0) ? A2:B2;
endmodule

module Mux3(sel3,A3,B3,Mux3_out);
	input         sel3;
	input  [31:0] A3,B3;
	output [31:0] Mux3_out;
	
	assign Mux3_out = (sel3==1'b0) ? A3:B3;
endmodule
	
// AND 
module AND_logic(branch, zero, and_out);
	input  branch,zero;
	output and_out;
	
	assign and_out = branch & zero;
endmodule

//Adder
module Adder(in_1,in_2,sum_out);
	input  [31:0] in_1,in_2;
	output [31:0] sum_out;
	
	assign sum_out =in_1 + in_2;
endmodule

//Interconecting All module
module top(clk, reset);
    input       clk, reset;
    wire [31:0] PC_top, instruction_top, RD1_top, RD2_top, ImmExt_top, Mux1_top, sum_out_top, nextPC_top, PC_in_top;
    wire [31:0] read_address_top, MemData_out_top, Write_data_top;
    wire        RegWrite_top, ALUSrc_top, zero_top, branch_top, and_out_top, MemtoReg_top, MemWrite_top, Memread_top;
    wire [1:0]  ALUOp_top;
    wire [3:0]  control_top;

    // Program Counter
    Program_counter PC(.clk(clk), 
						.reset(reset), 
						.PC_in(PC_in_top),
						.PC_out(PC_top));

    // PC Adder
    PCplus4 PC_Adder(.fromPC(PC_top), 
					.nextPC(nextPC_top));

    // Instruction Memory
    instruction_mem Inst_Memory(.clk(clk), 
								.reset(reset), 
								.read_address(PC_top),
								.instruction_out(instruction_top));

    // Register File
    Reg_file Reg_file(.clk(clk),
						.reset(reset), 
						.RegWrite(RegWrite_top), 
						.Rs1(instruction_top[19:15]), 
						.Rs2(instruction_top[24:20]), 
						.Rd(instruction_top[11:7]), 
						.Write_data(Write_data_top), 
						.Read_data1(RD1_top),
						.Read_data2(RD2_top));

    // Immediate Generator
    ImmGen ImmGen(.opcode(instruction_top[6:0]), 
							.instruction(instruction_top), 
							.ImmExt(ImmExt_top));

    // Control Unit
    Control_unit Control_unit(.instruction(instruction_top[6:0]), 
								.Branch(branch_top), 
								.Memread(Memread_top), 
								.MemtoReg(MemtoReg_top),
								.ALUOp(ALUOp_top), 
								.MemWrite(MemWrite_top), 
								.ALUSrc(ALUSrc_top), 
								.RegWrite(RegWrite_top));

    // ALU Control
    ALU_Control ALU_Control(.ALUOp(ALUOp_top),
							.fun7(instruction_top[30]), 
							.fun3(instruction_top[14:12]),
							.Control_out(control_top));

    // ALU
    ALU_unit ALU(.A(RD1_top),
					.B(Mux1_top), 
					.Control_in(control_top),
					.ALU_Result(read_address_top),
					.zero(zero_top));

    // ALU Mux
    Mux1 ALU_mux(.sel1(ALUSrc_top),
					.A1(RD2_top),
					.B1(ImmExt_top),
					.Mux1_out(Mux1_top));

    // Adder
    Adder Adder(.in_1(PC_top), 
				.in_2(ImmExt_top), 
				.sum_out(sum_out_top));

    // AND Logic
    AND_logic AND(.branch(branch_top), 
					.zero(zero_top), 
					.and_out(and_out_top));

    // Mux for PC
    Mux2 PC_mux(.sel2(and_out_top), 
				.A2(nextPC_top), 
				.B2(sum_out_top), 
				.Mux2_out(PC_in_top));

    // Data Memory
    Data_Memory Data_memory(.clk(clk), 
							.reset(reset), 
							.MemWrite(MemWrite_top),
							.Memread(Memread_top),
							.read_address(read_address_top),
							.Write_data(RD2_top), 
							.MemData_out(MemData_out_top));

    // Mux for Write Data
    Mux3 Data_mux(.sel3(MemtoReg_top), 
					.A3(read_address_top),
					.B3(MemData_out_top), 
					.Mux3_out(Write_data_top));
endmodule




// Testbench
module tb_top;

    reg clk, reset;

    // Instantiate the top module (Unit Under Test)
    top uut(.clk(clk), .reset(reset));

    // Initial block for controlling the reset signal and simulation time
    initial begin
        clk = 0;    // Initialize clock to 0
        reset = 0;  // Initialize reset to 0 (inactive)
        
        // Start of simulation, assert reset after 5 time units
        #5 reset = 1;   // Assert reset (active)
        
        // Deassert reset after 10 time units
        #10 reset = 0;  // Deassert reset (inactive)
        
        // Let the simulation run for another 400 time units
        #400;
        
        // End the simulation after the delay
        $finish;
    end

    // Clock generation (50% duty cycle, clock period of 20 time units)
    always #10 clk = ~clk;
	
	initial begin
        // Dump waveforms to file for viewing in a waveform viewer
        $dumpfile("waveform.vcd");
        $dumpvars(0, tb_top);

        // Monitor changes in critical signals
        $monitor($time, " PC: %h, Instruction: %h, RD1: %h, RD2: %h, ALU_Result: %h, MemData_out: %h",
                          uut.PC_top, uut.instruction_top, uut.RD1_top, uut.RD2_top, uut.read_address_top, uut.MemData_out_top);
    end

endmodule


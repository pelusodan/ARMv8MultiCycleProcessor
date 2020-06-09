`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 06/02/2020 08:41:27 PM
// Design Name: 
// Module Name: cpu5arm
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

// cpu5arm dut(.reset(reset),.clk(clk),.iaddrbus(iaddrbus),.ibus(instrbus),.daddrbus(daddrbus),.databus(databus));
module cpu5arm(reset, clk, iaddrbus, ibus, daddrbus, databus);
    input reset, clk;
    input [31:0] ibus;
    inout [63:0] databus;
    output [63:0] iaddrbus, daddrbus;
    
    
    // PC and Ifid wires
    wire [63:0] muxToPc, pcAdderToMux, iaddrIfidToAdder, shiftLeftAdderToMux;
    wire [2:0] shiftInsDecoderToIdex;
    wire [31:0] instbusToDecoder ;
    wire [7:0] movShiftToMux;
    
    // wires leaving the decoder
    wire [5:0] AluInsDecToIdex;
    wire [2:0] checkBranchDecToCheckBranch, shiftInsDecToIdex;
    wire [1:0] equalizerDecToEqualizer, loadInsDecToIdex, loadInsIdexToExmem, loadInExmemToMemwb;
    wire loadInsMemwbToMux, cbOrBDecToCheckBranch; 
    
    // reg addresses
    wire [31:0] rdAddr, rmAddr, rnAddr, bSelectMuxToReg;
    
    // reg outputs
    wire [63:0] abusRegToIdex, bbusRegToIdex;
    
    // equalizer wires
    wire [31:0] DselectEqToIdex ;
    wire eqToCheckBranch;
    
    // checkbranch wires
    wire checkBranchToPcMux;
    
    // imm extender wires
    wire [63:0] immDecoderToIdex;
    
    // shamt wires
    wire [63:0] shamtToIdex;
    
    // idex outputs
    wire [63:0] abusIdexToAlu, bbusIdexToAlu, immIdexToAlu, shamtIdexToShifter;
    wire [1:0] loadSelectIdexToExmem;
    wire [2:0] shiftInsIdexToShifter;
    wire [31:0] DselectIdexToExmem;
    wire [5:0] AluInsIdexToAlu;
    
    // shift wires
    wire [63:0] shiftAInput, shiftToMux;
    
    // Imm or RM value
    wire [63:0] bbusMuxToAlu;
    
    // ALU outputs
    wire [63:0] aluToMux, muxToExmem;
    wire [5:0] flagsToCheckBranch;
    
    // EXmem outputs
    wire [31:0] dSelectExmemToMemwb;
    wire [63:0] databusExmemToBuffer;
    wire [1:0] loadSelectExmemToMemwb;
    
    // Memwb outputs
    wire loadWireMemwbToMux;
    wire [31:0] dSelectMemwbToRegfile;
    wire [63:0] daddrbusMemwbToMux, databusMemwbToMux, muxOutToReg;
    
    
    pcReg pc(
        .clk(clk),
        .iaddrbusIn(muxToPc),
        .iaddrbusOut(iaddrbus),
        .reset(reset)   
    );
    adder pcAdder(
        .a(iaddrbus),
        .b(64'h0000000000000004),
        .d(pcAdderToMux)
    );
    ifidReg ifid(
        .ibusIn(ibus),
        .clk(clk),
        .ibusOut(instbusToDecoder),
        .iaddrbusIn(pcAdderToMux),
        .iaddrbusOut(iaddrIfidToAdder)
    );
    adder shiftIaddrAdder(
        .a(iaddrIfidToAdder-4),// we need to subtract 4 because in ARM it's PC + branch (unlike mips which is pc + 4 + branch)
        .b(immDecoderToIdex),
        .d(shiftLeftAdderToMux)
    );
    // if equal, then the next instruction will breanch to the shift
    mux2to1_64bit instrMux(
        .abus(pcAdderToMux),
        .bbus(shiftLeftAdderToMux),
        .S(checkBranchToPcMux),
        .out(muxToPc)
     );
     
     //module decoderTop(ibus, AluIns, shiftIns, checkBranch, equalizer, loadIns, cbOrB, rd, rn, rm);

    decoderTop top(
        .ibus(instbusToDecoder),
        .AluIns(AluInsDecToIdex),
        .shiftIns(shiftInsDecToIdex),
        .checkBranch(checkBranchDecToCheckBranch),
        .equalizer(equalizerDecToEqualizer),
        .loadIns(loadInsDecToIdex),
        .cbOrB(cbOrBDecToCheckBranch),
        .rd(rdAddr),
        .rn(rnAddr), 
        .rm(rmAddr)
    );
    // need to select from RT (same bits as RD) field if a CBZ,CBNZ,STUR calls, so we add a mux for this logic selected by CB enable bit
    mux2to1_32bit bSelectMux(
        .abus(rmAddr),
        .bbus(rdAddr),
        .S(equalizerDecToEqualizer[1] || (loadInsDecToIdex[1]&&!loadInsDecToIdex[0])), // if its a CBZ / CBNZ or if its a STUR call
        .out(bSelectMuxToReg)
    );
     regfile register(
         .Aselect(rnAddr),
         .Bselect(bSelectMuxToReg),
         .Dselect(dSelectMemwbToRegfile),
         .dbus(muxOutToReg),
         .clk(clk),
         .abus(abusRegToIdex),
         .bbus(bbusRegToIdex)
     );
     equalizer eq(
        .out(eqToCheckBranch),
        .DselectIn(rdAddr),
        .DselectOut(DselectEqToIdex),
        .en(equalizerDecToEqualizer[1]),
        .fxn(equalizerDecToEqualizer[0]),
        .rt(bbusRegToIdex),
        .loadSelectIn(loadInsDecToIdex)
     );
     checkBranch branchChecker(
        .eqIn(eqToCheckBranch), 
        .branchCode(checkBranchDecToCheckBranch), // {branchCode, en}
        .flags(flagsToCheckBranch),
        .out(checkBranchToPcMux),
        .cbOrB(cbOrBDecToCheckBranch)
     );
     immDecoder imm(
        .ibus(instbusToDecoder),
        // tells us how we should decode the IMM val {ALU (but not for SW), D, MOV, CondBranch, BranchIMM}                  
        .extOp({AluInsDecToIdex[0]&&!loadInsDecToIdex[1],loadInsDecToIdex[1],shiftInsDecToIdex[2],checkBranchDecToCheckBranch[0], cbOrBDecToCheckBranch}),
        .out(immDecoderToIdex)
     );
     shamtDecoder shamt(
        .ibus(instbusToDecoder),
        .shiftIns(shiftInsDecToIdex),
        .out(shamtToIdex)
     );
     idexReg idex(
         .clk(clk),
         .abusIn(abusRegToIdex),
         .abusOut(abusIdexToAlu),
         .bbusIn(bbusRegToIdex),
         .bbusOut(bbusIdexToAlu),
         .loadSelectIn(loadInsDecToIdex),
         .loadSelectOut(loadSelectIdexToExmem),
         .shiftInsIn(shiftInsDecToIdex),
         .shiftInsOut(shiftInsIdexToShifter),
         .AluInsIn(AluInsDecToIdex),
         .AluInsOut(AluInsIdexToAlu),
         .DselectIn(DselectEqToIdex),
         .DselectOut(DselectIdexToExmem),
         .ImmIn(immDecoderToIdex),
         .ImmOut(immIdexToAlu),
         .shamtIn(shamtToIdex),
         .shamtOut(shamtIdexToShifter)
     );
     mux2to1_64bit muxLeftShiftInput(
        .abus(abusIdexToAlu),
        .bbus(immIdexToAlu),
        .S(shiftInsIdexToShifter[2]), // 0 when LSR / LSL, 1 when MOVR
        .out(shiftAInput)
     );
     shifter shift(
        .a(shiftAInput),
        .b(shamtIdexToShifter),
        .s(shiftInsIdexToShifter[1]), // 0 when left shift, 1 when right
        .d(shiftToMux)
     );

     mux2to1_64bit immSelect(
         .abus(bbusIdexToAlu),
         .bbus(immIdexToAlu),
         .S(AluInsIdexToAlu[0]),// 0 when R format, 1 when I
         .out(bbusMuxToAlu)
     );
     alu64 alu(
         .d(aluToMux),
         .a(abusIdexToAlu),
         .b(bbusMuxToAlu),
         .Cin(AluInsIdexToAlu[2]),
         .S(AluInsIdexToAlu[5:3]),
         .flags(flagsToCheckBranch)
     );
     mux2to1_64bit muxAluShift(
          .abus(aluToMux),
          .bbus(shiftToMux),
          .S(shiftInsIdexToShifter[0]), // 1 when use shifting, 0 when alu out
          .out(muxToExmem)
      );
     exmemReg exmem(
         .aluResultIn(muxToExmem),
         .aluResultOut(daddrbus),
         .clk(clk),
         .dSelectIn(DselectIdexToExmem),
         .dSelectOut(dSelectExmemToMemwb),
         .loadSelectIn(loadSelectIdexToExmem),
         .loadSelectOut(loadSelectExmemToMemwb),
         .databusIn(bbusIdexToAlu),
         .databusOut(databusExmemToBuffer)
     );
     triStateBuffer buffer(
         .S(loadSelectExmemToMemwb),
         .in(databusExmemToBuffer),
         .out(databus)
     );
     memwbReg memwb(
         .daddrbusIn(daddrbus),
         .daddrbusOut(daddrbusMemwbToMux),
         .databusIn(databus),
         .databusOut(databusMemwbToMux),
         .loadSelectIn(loadSelectExmemToMemwb[0]),
         .loadSelectOut(loadWireMemwbToMux),
         .DselectIn(dSelectExmemToMemwb),
         .DselectOut(dSelectMemwbToRegfile),
         .clk(clk)
     );
     mux2to1_64bit writebackMux(
         .abus(daddrbusMemwbToMux),
         .bbus(databusMemwbToMux),
         .S(loadWireMemwbToMux),
         .out(muxOutToReg)
     );
endmodule

// MEMWB REGISTER
module memwbReg(daddrbusIn, daddrbusOut, databusIn, databusOut, loadSelectIn, loadSelectOut, clk, DselectIn, DselectOut);
    input [31:0] DselectIn;
    input [63:0] daddrbusIn, databusIn;
    input loadSelectIn, clk;
    output reg [31:0]  DselectOut;
    output reg [63:0] daddrbusOut, databusOut;
    output reg loadSelectOut;
    always @ (posedge clk) begin
        daddrbusOut = daddrbusIn;
        databusOut = databusIn;
        loadSelectOut = loadSelectIn;
        DselectOut = DselectIn;
    end
endmodule
//TRI STATE MODULE
module triStateBuffer(S,in,out);
    input [1:0] S;
    input [63:0] in;
    output [63:0] out;
    assign out = (S==2'b00 || S==2'b10) ? in : 64'bz;   
endmodule
// EXMEM
module exmemReg(aluResultIn,aluResultOut,clk,dSelectIn,dSelectOut,loadSelectIn,loadSelectOut,databusIn,databusOut);
    input [63:0] aluResultIn, databusIn;
    input [31:0] dSelectIn;
    input clk;
    input [1:0] loadSelectIn;
    output reg [63:0] aluResultOut, databusOut;
    output reg [31:0] dSelectOut;
    output reg [1:0] loadSelectOut;
    always @ (posedge clk) begin
        aluResultOut = aluResultIn;
        databusOut = databusIn;
        loadSelectOut = loadSelectIn;
        dSelectOut = dSelectIn;
    end
endmodule
// SHIFTER MODULE
module shifter(a,b,s,d);
    input [63:0] a, b;
    input s;
    output [63:0] d;
    assign d = s ? a>>>b : a<<b;
endmodule

//MUX 
module mux2to1_32bit(abus,bbus,S,out);
    input [31:0] abus, bbus;
    input S;
    output [31:0] out;
    wire sWire;
    assign sWire = (S===1'bx) ? 0 : S;
    assign out = sWire ? bbus: abus;
endmodule
module mux2to1_64bit(abus,bbus,S,out);
    input [63:0] abus, bbus;
    input S;
    output [63:0] out;
    wire sWire;
    assign sWire = (S===1'bx) ? 0 : S;
    assign out = sWire ? bbus: abus;
endmodule
// ALU
module alu64 (d, flags, a, b, Cin, S);
   output[63:0] d;
   output [3:0] flags;
   input [63:0] a, b;
   input Cin;
   input [2:0] S;   
   wire [63:0] c, g, p;
   wire gout, pout;
   alu_cell alucell[63:0] (
      .d(d),
      .g(g),
      .p(p),
      .a(a),
      .b(b),
      .c(c),
      .S(S)
   );
   lac6 laclevel5(
      .c(c),
      .gout(gout),
      .pout(pout),
      .Cin(Cin),
      .g(g),
      .p(p)
   );
   overflow over(
      .gout(gout),
      .pout(pout),
      .Cin(Cin),
      .c31(c[31]),
      .Cout(flags[0]),
      .V(flags[1])
   );
   // zero
   assign flags[2]= d==0 ? 1'b1 : 1'b0;
   // negative
   assign flags[3]= d[63]==1'b1 ? 1'b1 : 1'b0;
endmodule
module alu_cell (d, g, p, a, b, c, S);
   output d, g, p;
   input a, b, c;
   input [2:0] S;      
   reg g,p,d,cint,bint;
     
   always @(a,b,c,S,p,g) begin 
     bint = S[0] ^ b;
     g = a & bint;
     p = a ^ bint;
     cint = S[1] & c;
     if(S[2] == 0)
        d = p ^ cint;
     if(S[2] == 1 && S[1] == 0 && S[0] == 0)
        d = a | b;
     if(S[2] == 1 && S[1] == 0 && S[0] == 1)
        d = !(a | b);
     if(S[2] == 1 && S[1] == 1 && S[0] == 0)
        d = a & b;
   end
endmodule
module overflow (gout,pout,Cin,c31,Cout,V);
    input gout, pout, Cin, c31;
    output Cout, V;
    assign Cout = gout | (pout & Cin);
    assign V = Cout ^ c31;
endmodule
module lac(c, gout, pout, Cin, g, p);
   output [1:0] c;
   output gout;
   output pout;
   input Cin;
   input [1:0] g;
   input [1:0] p;
   assign c[0] = Cin;
   assign c[1] = g[0] | ( p[0] & Cin );
   assign gout = g[1] | ( p[1] & g[0] );
   assign pout = p[1] & p[0];	
endmodule
module lac2 (c, gout, pout, Cin, g, p);
   output [3:0] c;
   output gout, pout;
   input Cin;
   input [3:0] g, p;
   
   wire [1:0] cint, gint, pint;
   
   lac leaf0(
      .c(c[1:0]),
      .gout(gint[0]),
      .pout(pint[0]),
      .Cin(cint[0]),
      .g(g[1:0]),
      .p(p[1:0])
   );
   
   lac leaf1(
      .c(c[3:2]),
      .gout(gint[1]),
      .pout(pint[1]),
      .Cin(cint[1]),
      .g(g[3:2]),
      .p(p[3:2])
   );
   
   lac root(
      .c(cint),
      .gout(gout),
      .pout(pout),
      .Cin(Cin),
      .g(gint),
      .p(pint)
   );
endmodule   
module lac3 (c, gout, pout, Cin, g, p);
   output [7:0] c;
   output gout, pout;
   input Cin;
   input [7:0] g, p;
   
   wire [1:0] cint, gint, pint;
   
   lac2 leaf0(
      .c(c[3:0]),
      .gout(gint[0]),
      .pout(pint[0]),
      .Cin(cint[0]),
      .g(g[3:0]),
      .p(p[3:0])
   );
   
   lac2 leaf1(
      .c(c[7:4]),
      .gout(gint[1]),
      .pout(pint[1]),
      .Cin(cint[1]),
      .g(g[7:4]),
      .p(p[7:4])
   );
   
   lac root(
      .c(cint),
      .gout(gout),
      .pout(pout),
      .Cin(Cin),
      .g(gint),
      .p(pint)
   );
endmodule
module lac4 (c, gout, pout, Cin, g, p);
 output [15:0] c;
 output gout, pout;
 input Cin;
 input [15:0] g, p;
 
 wire [1:0] cint, gint, pint;
 
 lac3 leaf0(
    .c(c[7:0]),
    .gout(gint[0]),
    .pout(pint[0]),
    .Cin(cint[0]),
    .g(g[7:0]),
    .p(p[7:0])
 );
 
 lac3 leaf1(
    .c(c[15:8]),
    .gout(gint[1]),
    .pout(pint[1]),
    .Cin(cint[1]),
    .g(g[15:8]),
    .p(p[15:8])
 );
 
 lac root(
    .c(cint),
    .gout(gout),
    .pout(pout),
    .Cin(Cin),
    .g(gint),
    .p(pint)
 );
endmodule
module lac5 (c, gout, pout, Cin, g, p);
output [31:0] c;
 output gout, pout;
 input Cin;
 input [31:0] g, p;
 
 wire [1:0] cint, gint, pint;
 
 lac4 leaf0(
    .c(c[15:0]),
    .gout(gint[0]),
    .pout(pint[0]),
    .Cin(cint[0]),
    .g(g[15:0]),
    .p(p[15:0])
 );
 
 lac4 leaf1(
    .c(c[31:16]),
    .gout(gint[1]),
    .pout(pint[1]),
    .Cin(cint[1]),
    .g(g[31:16]),
    .p(p[31:16])
 );
 
 lac root(
    .c(cint),
    .gout(gout),
    .pout(pout),
    .Cin(Cin),
    .g(gint),
    .p(pint)
 );
endmodule
module lac6 (c, gout, pout, Cin, g, p);
output [63:0] c;
 output gout, pout;
 input Cin;
 input [63:0] g, p;
 
 wire [1:0] cint, gint, pint;
 
 lac5 leaf0(
    .c(c[31:0]),
    .gout(gint[0]),
    .pout(pint[0]),
    .Cin(cint[0]),
    .g(g[31:0]),
    .p(p[31:0])
 );
 
 lac5 leaf1(
    .c(c[63:32]),
    .gout(gint[1]),
    .pout(pint[1]),
    .Cin(cint[1]),
    .g(g[63:32]),
    .p(p[63:32])
 );
 
 lac root(
    .c(cint),
    .gout(gout),
    .pout(pout),
    .Cin(Cin),
    .g(gint),
    .p(pint)
 );
endmodule
// IDEX REGISTER
module idexReg(clk, abusIn, abusOut, bbusIn, bbusOut, loadSelectIn, loadSelectOut, shiftInsIn, shiftInsOut, AluInsIn, AluInsOut, DselectIn, DselectOut, shamtIn, shamtOut, ImmIn, ImmOut);
    input clk;
    input [63:0] abusIn, bbusIn, shamtIn, ImmIn;
    input [31:0] DselectIn;
    input [5:0] AluInsIn;
    input [2:0] shiftInsIn;
    input [1:0] loadSelectIn; 
    output reg [63:0] abusOut, bbusOut, shamtOut, ImmOut;
    output reg [31:0] DselectOut;
    output reg [5:0] AluInsOut;
    output reg [2:0] shiftInsOut;
    output reg [1:0] loadSelectOut; 
        always  @ (posedge clk) begin
            abusOut = abusIn;
            bbusOut = bbusIn;
            loadSelectOut = loadSelectIn;
            shiftInsOut = shiftInsIn;
            AluInsOut = AluInsIn;
            DselectOut = DselectIn;
            shamtOut = shamtIn;
            ImmOut = ImmIn;
        end
endmodule
// SHAMT - returns either 
module shamtDecoder(ibus, out, shiftIns);
    input [31:0] ibus;
    input [2:0] shiftIns;
    output [63:0] out;
    //              LSR and LSL    shamt           quad MOV amt
    assign out = !shiftIns[2] ?  ibus[15:10] : ibus[22:21]*16;
endmodule;
// IMMEXTENDER
module immDecoder(ibus,extOp,out);
    input [31:0] ibus;
    input [4:0] extOp;
    output [63:0] out;
    assign out = extOp[4] ? {52'b0,ibus[21:10]} : // ALUImm
        extOp[3] ? {{55{ibus[20]}},ibus[20:12]} : // DT_Addr
        extOp[2] ? {48'b0,ibus[20:5]} : // MovImm
        extOp[1] ? {{43{ibus[23]}},ibus[23:5],2'b0}:// CondBranchAddr
        extOp[0] ? {{36{ibus[25]}},ibus[25:0], 2'b0}:// BranchImm
        63'bz; // default
endmodule
// CHECKBRANCH
module checkBranch(eqIn, branchCode, flags, out, cbOrB);
    input eqIn, cbOrB;
    output out;
    input [2:0] branchCode;
    input [3:0] flags;
    //   {Negative,Zero,Overflow,CarryOver}
    // eqIn from CBZ or CBNZ and cbOrB for Branch stmts
    assign out = eqIn || cbOrB ||
    (branchCode==3'b001 && flags[1]) || // BEQ
    (branchCode==3'b011 && !flags[1]) || // BNE
    (branchCode==3'b101 && flags[3]!=flags[1]) || // BLT
    (branchCode==3'b111 && flags[3]==flags[1] && !flags[2]) ? 1'b1 : 1'b0; // BLT (Z==0) && (N==V) and default
endmodule
//EQUALIZER                                     enable function
module equalizer(DselectIn,DselectOut, rt, en, fxn, out, loadSelectIn);
    input [31:0] DselectIn;
    input [63:0] rt;
    input [1:0] loadSelectIn; // for setting Dselect to null register when STUR
    // 10 = CBZ, 11 = CBNZ
    input en, fxn;
    output out;
    output [31:0] DselectOut;
    assign out = !en ? 0 : // default - not branching
    (rt == 0 && fxn ==0) ?  1: // CBZ function
    (rt != 0 && fxn==1) ? 1: 0; // CBNZ function and the final default, 0
    // for avoiding WB in CBZ and CBNZ, redirect to the zero register 
    assign DselectOut = !en ? DselectIn:
     (rt == 0 && fxn == 0)||(rt != 0 && fxn == 1) ? 64'h8000000000000000:
     loadSelectIn==2'b10 ? 64'h8000000000000000 : DselectIn; // disable wb for STUR
endmodule
// REGISTER FILE
module regfile(Aselect,Bselect,Dselect,dbus,clk,abus,bbus);
    input [31:0] Aselect, Bselect, Dselect;
    input [63:0] dbus;
    input clk;
    output [63:0] abus, bbus;
    // changed 0 reg from r0 to r31        
    negdffcell register_cells [30:0](
        .Aselect(Aselect[30:0]),
        .Bselect(Bselect[30:0]),
        .clk(clk),
        .Dselect(Dselect[30:0]),
        .dbus(dbus),
        .abus(abus),
        .bbus(bbus)
        );
    nullcell final_cell (
        .Aselect(Aselect[31]),
        .Bselect(Bselect[31]),
        .abus(abus),
        .bbus(bbus)
    );
endmodule                           // we'll ignore the Dselect and dbus because we're not writing to anything here
module nullcell(Aselect,Bselect,abus,bbus);
    input Aselect, Bselect;
    output [63:0] abus, bbus;
    assign abus = Aselect ? 0 : 64'bz;
    assign bbus = Bselect ? 0 : 64'bz;
endmodule
module negdffcell(Aselect,Bselect,clk,Dselect,dbus,abus,bbus);
    input Aselect, Bselect, clk, Dselect;
    input [63:0] dbus;
    output [63:0] abus, bbus;
    wire [63:0] Q;
    negdff flip(
        .D(dbus),
        .clk(clk),
        .Dselect(Dselect),
        .Q(Q)
        );
    buffer cellbuffer(
        .Q(Q),
        .Aselect(Aselect),
        .Bselect(Bselect),
        .abus(abus),
        .bbus(bbus)
    );
endmodule
module negdff(D,clk,Dselect,Q);
    input [63:0] D;
    input clk, Dselect;
    output reg [63:0] Q;
    wire newclk;
    assign newclk = clk & Dselect;
    always @(negedge newclk) begin
        if (Dselect==1'b1) Q = D;
    end
endmodule
module buffer(Q,Aselect,Bselect,abus,bbus);
    input [63:0] Q;
    input Aselect, Bselect;
    output [63:0] abus,bbus;
    assign abus = Aselect ? Q : 64'bz;
    assign bbus = Bselect ? Q : 64'bz;
endmodule
// DECODER
module decoderTop(ibus, AluIns, shiftIns, checkBranch, equalizer, loadIns, cbOrB, rd, rn, rm);
    input [31:0] ibus;
    output [5:0] AluIns;
    output [2:0] shiftIns, checkBranch;
    output [1:0] equalizer, loadIns;
    output cbOrB;
    output [31:0] rd, rn, rm;    
    // still need to read QUAD code for MOV and wire to mux with 0,16,32,48
    dec5to32 rmDec(
        .in(ibus[20:16]),
        .out(rm));
    dec5to32 rnDec(
        .in(ibus[9:5]),
        .out(rn));
    dec5to32 rdDec(
        .in(ibus[4:0]),
        .out(rd));
    opcodeDec opcodedec(
        .ibus(ibus),
        .AluInst(AluIns),
        .shiftIns(shiftIns),
        .checkBranch(checkBranch),
        .equalizer(equalizer),
        .loadIns(loadIns),
        .cbOrB(cbOrB)
    ); 
endmodule
module dec5to32(in,out);
    input [4:0] in;
    output reg [31:0] out;
    always @(in, out) begin
       case(in)
       5'b00000: out = 32'b00000000000000000000000000000001; 
       5'b00001: out = 32'b00000000000000000000000000000010; 
       5'b00010: out = 32'b00000000000000000000000000000100;
       5'b00011: out = 32'b00000000000000000000000000001000;
       5'b00100: out = 32'b00000000000000000000000000010000;
       5'b00101: out = 32'b00000000000000000000000000100000;
       5'b00110: out = 32'b00000000000000000000000001000000;
       5'b00111: out = 32'b00000000000000000000000010000000;
       5'b01000: out = 32'b00000000000000000000000100000000;
       5'b01001: out = 32'b00000000000000000000001000000000;
       5'b01010: out = 32'b00000000000000000000010000000000;
       5'b01011: out = 32'b00000000000000000000100000000000;
       5'b01100: out = 32'b00000000000000000001000000000000;
       5'b01101: out = 32'b00000000000000000010000000000000;
       5'b01110: out = 32'b00000000000000000100000000000000;
       5'b01111: out = 32'b00000000000000001000000000000000;
       5'b10000: out = 32'b00000000000000010000000000000000;
       5'b10001: out = 32'b00000000000000100000000000000000;
       5'b10010: out = 32'b00000000000001000000000000000000;
       5'b10011: out = 32'b00000000000010000000000000000000;
       5'b10100: out = 32'b00000000000100000000000000000000;
       5'b10101: out = 32'b00000000001000000000000000000000;
       5'b10110: out = 32'b00000000010000000000000000000000;
       5'b10111: out = 32'b00000000100000000000000000000000;
       5'b11000: out = 32'b00000001000000000000000000000000;
       5'b11001: out = 32'b00000010000000000000000000000000;
       5'b11010: out = 32'b00000100000000000000000000000000;
       5'b11011: out = 32'b00001000000000000000000000000000;
       5'b11100: out = 32'b00010000000000000000000000000000;
       5'b11101: out = 32'b00100000000000000000000000000000;
       5'b11110: out = 32'b01000000000000000000000000000000;
       5'b11111: out = 32'b10000000000000000000000000000000;
       endcase
    end
endmodule 
module opcodeDec(ibus,AluInst,shiftIns, checkBranch, equalizer, loadIns, cbOrB);
    input [31:0] ibus;
    output reg [5:0] AluInst;
    output reg [2:0] shiftIns, checkBranch;
    output reg [1:0] equalizer, loadIns;
    output reg cbOrB;
    always @ (ibus, AluInst,shiftIns, checkBranch, equalizer, loadIns, cbOrB) begin
        case(ibus[31:21])
            // R Format
            // ADD                     
            // ALUInst = {AluSelector,Cin,enableSetFlags,Imm}, shiftIns ={shiftOpOrMOV,leftOrRightShift,en}, checkBranch={branchOpSelector,en}, equalizer={notZeroOrZero,en}, loadIns={en,storeOrLoad}
            11'b10001011000:  begin AluInst=6'b010000; shiftIns=3'b000; checkBranch=3'b000; equalizer=2'b00; loadIns=2'b00; cbOrB=1'b0; end 
            // AND
            11'b10001010000:  begin AluInst=6'b110000; shiftIns=3'b000; checkBranch=3'b000; equalizer=2'b00; loadIns=2'b00; cbOrB=1'b0; end
            
            // LSL                                      001 tells us logical shift left into rd
            11'b11010011011:  begin AluInst=6'b000000; shiftIns=3'b001; checkBranch=3'b000; equalizer=2'b00; loadIns=2'b00; cbOrB=1'b0; end
            // LSR                                      011 tells us logical shift right into rd
            11'b11010011010:  begin AluInst=6'b000000; shiftIns=3'b011; checkBranch=3'b000; equalizer=2'b00; loadIns=2'b00; cbOrB=1'b0; end
            // EOR
            11'b11001010000:  begin AluInst=6'b000000; shiftIns=3'b000; checkBranch=3'b000; equalizer=2'b00; loadIns=2'b00; cbOrB=1'b0; end
            // ORR
            11'b10101010000:  begin AluInst=6'b100000; shiftIns=3'b000; checkBranch=3'b000; equalizer=2'b00; loadIns=2'b00; cbOrB=1'b0; end
            // SUB
            11'b11001011000:  begin AluInst=6'b011100; shiftIns=3'b000; checkBranch=3'b000; equalizer=2'b00; loadIns=2'b00; cbOrB=1'b0; end
            
            // ADDS                             set flags = true
            11'b10101011000:  begin AluInst=6'b010010; shiftIns=3'b000; checkBranch=3'b000; equalizer=2'b00; loadIns=2'b00; cbOrB=1'b0; end
            // ANDS
            11'b11101010000:  begin AluInst=6'b110010; shiftIns=3'b000; checkBranch=3'b000; equalizer=2'b00; loadIns=2'b00; cbOrB=1'b0; end
            // SUBS
            11'b11101011000:  begin AluInst=6'b011110; shiftIns=3'b000; checkBranch=3'b000; equalizer=2'b00; loadIns=2'b00; cbOrB=1'b0; end
           
            // D Format
            // STUR                           +,0,0,true                                                    lw = 11, sw = 10                  
            11'b11111000000:  begin AluInst=6'b010001; shiftIns=3'b000; checkBranch=3'b000; equalizer=2'b00; loadIns=2'b10; cbOrB=1'b0; end
            // LDUR
            11'b11111000010:  begin AluInst=6'b010001; shiftIns=3'b000; checkBranch=3'b000; equalizer=2'b00; loadIns=2'b11; cbOrB=1'b0; end
            default:
                case(ibus[31:22])
                    // I Format
                    // ADDI                             Imm = true
                    10'b1001000100: begin AluInst=6'b010001; shiftIns=3'b000; checkBranch=3'b000; equalizer=2'b00; loadIns=2'b00; cbOrB=1'b0; end 
                    // ANDI
                    10'b1001001000: begin AluInst=6'b110001; shiftIns=3'b000; checkBranch=3'b000; equalizer=2'b00; loadIns=2'b00; cbOrB=1'b0; end
                    // ADDIS
                    10'b1011000100: begin AluInst=6'b010011; shiftIns=3'b000; checkBranch=3'b000; equalizer=2'b00; loadIns=2'b00; cbOrB=1'b0; end 
                    // ANDIS
                    10'b1111001000: begin AluInst=6'b110011; shiftIns=3'b000; checkBranch=3'b000; equalizer=2'b00; loadIns=2'b00; cbOrB=1'b0; end
                    // EORI
                    10'b1101001000: begin AluInst=6'b000001; shiftIns=3'b000; checkBranch=3'b000; equalizer=2'b00; loadIns=2'b00; cbOrB=1'b0; end
                    // ORRI
                    10'b1011001000: begin AluInst=6'b100001; shiftIns=3'b000; checkBranch=3'b000; equalizer=2'b00; loadIns=2'b00; cbOrB=1'b0; end
                    // SUBI
                    10'b1101000100: begin AluInst=6'b011101; shiftIns=3'b000; checkBranch=3'b000; equalizer=2'b00; loadIns=2'b00; cbOrB=1'b0; end
                    // SUBIS
                    10'b1111000100: begin AluInst=6'b011111; shiftIns=3'b000; checkBranch=3'b000; equalizer=2'b00; loadIns=2'b00; cbOrB=1'b0; end
                    default:
                        case(ibus[31:23])
                            // IM Format
                            // MOVZ                                     100 tells us MOV shift
                            9'b110100101:  begin AluInst=6'b000000; shiftIns=3'b101; checkBranch=3'b000; equalizer=2'b00; loadIns=2'b00; cbOrB=1'b0; end
                            default:
                                case(ibus[31:24])
                                    // CB Format
                                    // CBNZ                                                                         11 - CBNZ                // to select CB format                                              
                                    8'b10110101: begin AluInst=6'b000000; shiftIns=3'b000; checkBranch=3'b001; equalizer=2'b11; loadIns=2'b00; cbOrB=1'b0; end
                                    // CBZ                                                                          10 - CBZ
                                    8'b10110100: begin AluInst=6'b000000; shiftIns=3'b000; checkBranch=3'b001; equalizer=2'b10; loadIns=2'b00; cbOrB=1'b0; end
                                    // BEQ                                                   beq = {00 , en}
                                    8'b01010101:  begin AluInst=6'b000000; shiftIns=3'b000; checkBranch=3'b001; equalizer=2'b00; loadIns=2'b00; cbOrB=1'b0; end
                                    // BNE                                                   bne = {01 , en}
                                    8'b01010110:  begin AluInst=6'b000000; shiftIns=3'b000; checkBranch=3'b011; equalizer=2'b00; loadIns=2'b00; cbOrB=1'b0; end                         
                                    // BLT                                                   blt = {10, en}
                                    8'b01010111:  begin AluInst=6'b000000; shiftIns=3'b000; checkBranch=3'b101; equalizer=2'b00; loadIns=2'b00; cbOrB=1'b0; end
                                    // BGE                                                   bge = {11, en}
                                    8'b01011000:  begin AluInst=6'b000000; shiftIns=3'b000; checkBranch=3'b011; equalizer=2'b00; loadIns=2'b00; cbOrB=1'b0; end
                                    default:
                                        case(ibus[31:26])
                                            // B Format
                                            // B                                                                                                        finally notify some MUXs to branch to BRaddr
                                            6'b000101: begin AluInst=6'b000000; shiftIns=3'b000; checkBranch=3'b000; equalizer=2'b00; loadIns=2'b00; cbOrB=1'b1; end
                                            default: begin AluInst=6'b000000; shiftIns=3'b000; checkBranch=3'b000; equalizer=2'b00; loadIns=2'b00; cbOrB=1'b0; end
                                        endcase
                                endcase 
                        endcase        
                endcase
        endcase
    end
endmodule
// IFID REGISTER
module ifidReg(ibusIn, clk, ibusOut, iaddrbusIn, iaddrbusOut);
    input [31:0] ibusIn;
    input [63:0] iaddrbusIn;
    input clk;
    output reg [31:0] ibusOut;
    output reg [63:0] iaddrbusOut;
    always @(posedge clk)
    begin
        ibusOut = ibusIn;
        iaddrbusOut = iaddrbusIn;
    end
endmodule
//ADDER
module adder(a, b, d);
    input [63:0] a, b;
    output [63:0] d;
    assign d = a + b;
endmodule
//PC REGISTER
module pcReg(clk, iaddrbusIn, iaddrbusOut, reset);
    input clk, reset;
    input [63:0] iaddrbusIn;
    output reg [63:0] iaddrbusOut;
    always @ (posedge clk)  begin
        if(reset) iaddrbusOut = 0;
        else iaddrbusOut = iaddrbusIn;
    end
endmodule

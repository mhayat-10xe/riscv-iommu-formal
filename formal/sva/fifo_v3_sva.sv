module fifo_v3_SVA #(
    parameter bit          FALL_THROUGH = 1'b0, // fifo is in fall-through mode
    parameter int unsigned DATA_WIDTH   = 32,   // default data width if the fifo is of type logic
    parameter int unsigned DEPTH        = 8,    // depth can be arbitrary from 0 to 2**32
    parameter type dtype                = logic [DATA_WIDTH-1:0],
    // DO NOT OVERWRITE THIS PARAMETER
    parameter int unsigned ADDR_DEPTH   = (DEPTH > 1) ? $clog2(DEPTH) : 1
)(
    input  logic  clk_i,            // Clock
    input  logic  rst_ni,           // Asynchronous reset active low
    input  logic  flush_i,          // flush the queue
    input  logic  testmode_i,       // test_mode to bypass clock gating
    // status flags
    input logic  full_o,           // queue is full
    input logic  empty_o,          // queue is empty
    input logic  [ADDR_DEPTH-1:0] usage_o,  // fill pointer
    // as long as the queue is not full we can push new data
    input  dtype  data_i,           // data to push into the queue
    input  logic  push_i,           // data is valid and can be pushed to the queue
    // as long as the queue is not empty we can pop new elements
    input dtype  data_o,           // output data
    input  logic  pop_i             // pop head from queue
);

default clocking @(posedge clk_i); endclocking
default disable iff (~rst_ni || flush_i);

logic [DATA_WIDTH-1:0] symbolic_data;

logic incr, decr;
int smart_tracker;
assign incr = push_i && !full_o && !data_sampled;
assign decr = pop_i  && !empty_o && !sampled_out;

always @(posedge clk_i or negedge rst_ni) 
    if (!rst_ni || flush_i) 
        smart_tracker <= 0;
    else 
        smart_tracker <= smart_tracker + incr - decr;    

logic ready_to_sample_in_data, data_sampled, sampled_out, must_read;

if(!FALL_THROUGH)
    assign must_read = (smart_tracker == 2) && decr && data_sampled;
else
    assign must_read = (smart_tracker == 2) && decr && data_sampled;

assign ready_to_sample_in_data = (symbolic_data == data_i) && push_i && !data_sampled;

always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni || flush_i) begin
        sampled_out   <= 0;
        data_sampled  <= 0;
    end
    else begin
        sampled_out   <= sampled_out  || must_read;
        data_sampled  <= data_sampled || ready_to_sample_in_data;
    end
end

//----------------------------assumptions started-----------------------------
    assmp1_stable_data:
    assume property ($stable(symbolic_data) && !flush_i);

    assmp2_full:
    assume property(full_o |-> !push_i || pop_i);  // Do not push when full unless pop is also high

    assmp3_empty:
    assume property(empty_o |-> !pop_i);          // Do not pop data when empty_o is high.

//----------------------------assumptions started-----------------------------

//----------------------------assertons started-----------------------------
generate
for (genvar i = 0; i < DATA_WIDTH; i++) begin
asrt1_ordering_nd_data_integrity:
assert property (must_read |=> (data_o[i] == symbolic_data[i]));

if(!FALL_THROUGH)
    asrt2_first_entry: // if symbolic data come in first fifo entry and fallthorugh is zero then in next cycle without pop data must come
    assert property(smart_tracker == 0 && ready_to_sample_in_data |=> (data_o[i] == symbolic_data[i])); 
else
    asrt2_first_entry: // if symbolic data come in first fifo entry and fallthorugh is one then in that cycle without pop data must come
    assert property(smart_tracker == 0 && ready_to_sample_in_data  |-> (data_o[i] == symbolic_data[i])); 
end
endgenerate

asrt3_eventually_full: // DEPTH_BITS writes to an empty FIFO without any pops will make it full.
assert property ( empty_o ##1 (push_i && !pop_i)[*DEPTH] |=> full_o);

asrt4_eventually_empty: // DEPTH_BITS pops to a full FIFO without any pushes will make it empty.
assert property (full_o ##1 (!push_i && pop_i)[*DEPTH] |=> empty_o); 
//----------------------------assertons ended-----------------------------

endmodule
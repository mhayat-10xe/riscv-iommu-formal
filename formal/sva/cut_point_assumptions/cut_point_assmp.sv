`define ddtp_iommu_mode riscv_iommu.ddtp.iommu_mode.q
`define ddtp_busy riscv_iommu.ddtp.busy.q


`define ar_valid dev_tr_req_i.ar_valid
`define ar_ready dev_tr_resp_o.ar_ready

`define aw_valid dev_tr_req_i.aw_valid
`define aw_ready dev_tr_resp_o.aw_ready

// -------------------cutpoint assumptions started-------------
asmp1_fctl:
assume property(!riscv_iommu.fctl.gxl && !riscv_iommu.fctl.be && !riscv_iommu.fctl.wsi);

assmp2_zero_flush: // for now on we are not looking into cache so assume flush is 0
assume property (!riscv_iommu.flush_ddtc && !riscv_iommu.flush_pdtc && !riscv_iommu.flush_vma && !riscv_iommu.flush_vma && !riscv_iommu.flush_gvma);

assmp3_debug_0: // as debug mode is not supported so this is tied to 0
assume property (!riscv_iommu.dbg_if_ctl);
// Before writing to the ddtp, busy bit must be 0
// and to change the ddt levels, the iommu_mode must first be bare or off.

// assmp3_ddtp_write:
// assume property (`ddtp_iommu_mode > 1 && $changed(`ddtp_iommu_mode) |-> !$past(`ddtp_busy) && $past(`ddtp_iommu_mode) <=1 );

assmp3_ddtp_write:
assume property (`ddtp_iommu_mode < 5);

assmp3_ddtp_not_stable:
assume property (`ar_valid && !`ar_ready |=> $stable(riscv_iommu.ddtp.iommu_mode.q));

assmp4_ddtp_stable:
assume property (`aw_valid && !`aw_ready |=> $stable(riscv_iommu.ddtp.iommu_mode.q));

assmp5_length_small:
assume property (dev_tr_req_i.aw.len < 5 && dev_tr_req_i.ar.len < 5);
// assmp5_ddtp_stable_whole_time:
// assume property ($stable (riscv_iommu.ddtp.iommu_mode.q));

// assmp3_ddtp_not_zero:
// assume property (riscv_iommu.ttype == 1);
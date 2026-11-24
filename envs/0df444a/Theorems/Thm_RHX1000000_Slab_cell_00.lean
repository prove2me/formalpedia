-- Prove2me | Theorems.Thm_RHX1000000_Slab_cell_00
-- name    : RHX1000000.Slab.cell_00
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T08:15:34.719498+00:00
-- url     : https://prove2.me/theorems/23acb780-7651-4cac-826f-15d0e3a70260
-- title:
--   Slab cell 0 at height 1000000 is zero-free
-- statement:
--   Cell 0 of the slab data `RHX_Slab1000000Data` passes the framework's cell checker `Arb4.cellOK S 0 = true`: the evaluator run at the cell centre with $N=300001$ terms, the kernel check `ArbEcon.Off.checkCell` that $\zeta$ has no zero on the cell disc, and the cell geometry inside the slab.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000; extended to height 100000 by the RHX100000 problems) to height 1000000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_ArdaRS_Config64
import Definitions.Def_RHX1E6_RunC00
import Definitions.Def_RHX_RunChain
import Definitions.Def_RHX_RunSplit
import Definitions.Def_RHX_Slab1000000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open ArbEcon.Off

theorem RHX1000000.Slab.cell_00 : Arb4.cellOK RHX1000000.Slab.S 0 = true := by
  sorry

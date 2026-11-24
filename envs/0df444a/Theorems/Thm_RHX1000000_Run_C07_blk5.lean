-- Prove2me | Theorems.Thm_RHX1000000_Run_C07_blk5
-- name    : RHX1000000.Run.C07.blk5
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T08:57:50.241873+00:00
-- url     : https://prove2.me/theorems/87bc31c7-1b80-4a2b-b192-cc4027729938
-- title:
--   Evaluator run at the centre of slab cell 7 at height 1000000, block 5
-- statement:
--   The framework's offline Euler–Maclaurin evaluator with the configuration of slab cell 7 at height $10^6$, run for $30000$ steps from the state `S30`, ends in the state `S36` (states from the definitions `RHX1E6_RunC07`).
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000; extended to height 100000 by the RHX100000 problems) to height 1000000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_ArdaRS_Config64
import Definitions.Def_RHX1E6_RunC07
import Definitions.Def_RHX_RunChain
import Definitions.Def_RHX_RunSplit
import Definitions.Def_RHX_Slab1000000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open ArbEcon.Off

namespace RHX1000000.Run.C07

theorem blk5 : runO (ArbEcon.OrderK.cfg64 16384000025 14) (⟨7, 0, 8, 2 ^ 512, 256⟩ : ArbEcon.Off.OCfg) 30000 S30 = S36 := by
  sorry

end RHX1000000.Run.C07

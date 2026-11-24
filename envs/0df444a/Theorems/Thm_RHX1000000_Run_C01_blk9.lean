-- Prove2me | Theorems.Thm_RHX1000000_Run_C01_blk9
-- name    : RHX1000000.Run.C01.blk9
-- status  : Open
-- author  : @@bwdaugherty
-- created : 2026-11-24T08:24:44.226876+00:00
-- url     : https://prove2.me/theorems/f45d0ae3-6fa2-4c28-9b2b-b97dd002b3f2
-- title:
--   Evaluator run at the centre of slab cell 1 at height 1000000, block 9
-- statement:
--   The framework's offline Euler–Maclaurin evaluator with the configuration of slab cell 1 at height $10^6$, run for $29999$ steps from the state `S54`, ends in the state `S60` (states from the definitions `RHX1E6_RunC01`).
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000; extended to height 100000 by the RHX100000 problems) to height 1000000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_ArdaRS_Config64
import Definitions.Def_RHX1E6_RunC01
import Definitions.Def_RHX_RunChain
import Definitions.Def_RHX_RunSplit
import Definitions.Def_RHX_Slab1000000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open ArbEcon.Off

namespace RHX1000000.Run.C01

theorem blk9 : runO (ArbEcon.OrderK.cfg64 16384000025 14) (⟨23, 0, 40, 2 ^ 2560, 256⟩ : ArbEcon.Off.OCfg) 29999 S54 = S60 := by
  sorry

end RHX1000000.Run.C01

-- Prove2me | Theorems.Thm_RHX1000000_Run_C05_blk2
-- name    : RHX1000000.Run.C05.blk2
-- status  : Open
-- author  : @@bwdaugherty
-- created : 2026-11-24T08:44:50.296355+00:00
-- url     : https://prove2.me/theorems/fd1b370d-9f20-484a-bac6-184a302cc27b
-- title:
--   Evaluator run at the centre of slab cell 5 at height 1000000, block 2
-- statement:
--   The framework's offline Euler–Maclaurin evaluator with the configuration of slab cell 5 at height $10^6$, run for $30000$ steps from the state `S12`, ends in the state `S18` (states from the definitions `RHX1E6_RunC05`).
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000; extended to height 100000 by the RHX100000 problems) to height 1000000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_ArdaRS_Config64
import Definitions.Def_RHX1E6_RunC05
import Definitions.Def_RHX_RunChain
import Definitions.Def_RHX_RunSplit
import Definitions.Def_RHX_Slab1000000Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open ArbEcon.Off

namespace RHX1000000.Run.C05

theorem blk2 : runO (ArbEcon.OrderK.cfg64 16384000025 14) (⟨31, 0, 40, 2 ^ 2560, 256⟩ : ArbEcon.Off.OCfg) 30000 S12 = S18 := by
  sorry

end RHX1000000.Run.C05

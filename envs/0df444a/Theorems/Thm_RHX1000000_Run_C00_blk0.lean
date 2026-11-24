-- Prove2me | Theorems.Thm_RHX1000000_Run_C00_blk0
-- name    : RHX1000000.Run.C00.blk0
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T08:15:18.15506+00:00
-- url     : https://prove2.me/theorems/f387c4ef-d326-49ca-b102-5381846160ae
-- title:
--   Evaluator run at the centre of slab cell 0 at height 1000000, block 0
-- statement:
--   The framework's offline Euler–Maclaurin evaluator with the configuration of slab cell 0 at height $10^6$, run for $30000$ steps from its initial state, ends in the state `S6` (states from the definitions `RHX1E6_RunC00`).
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

namespace RHX1000000.Run.C00

theorem blk0 : runO (ArbEcon.OrderK.cfg64 16384000025 14) (⟨21, 0, 40, 2 ^ 2560, 256⟩ : ArbEcon.Off.OCfg) 30000 (StO.init (ArbEcon.OrderK.cfg64 16384000025 14) 5) = S6 := by
  sorry

end RHX1000000.Run.C00

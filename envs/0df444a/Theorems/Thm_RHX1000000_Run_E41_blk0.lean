-- Prove2me | Theorems.Thm_RHX1000000_Run_E41_blk0
-- name    : RHX1000000.Run.E41.blk0
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T04:41:27.425202+00:00
-- url     : https://prove2.me/theorems/56a82296-bbcd-404d-a5f1-d3ba860087ac
-- title:
--   Evaluator run at the centre of edge piece 41 at height 1000000, block 0
-- statement:
--   The framework's offline Euler–Maclaurin evaluator with the configuration of edge piece 41 at height $10^6$, run for $30000$ steps from its initial state, ends in the state `S6` (states from the definitions `RHX1E6_RunE41`).
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000; extended to height 100000 by the RHX100000 problems) to height 1000000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_ArdaRH65K_Turing121_H11K_EdgeSplit
import Definitions.Def_ArdaRS_Config64
import Definitions.Def_RHX1E6_RunE41
import Definitions.Def_RHX_Edge1000000Data
import Definitions.Def_RHX_RunChain
import Definitions.Def_RHX_RunSplit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open ArbEcon.Off

namespace RHX1000000.Run.E41

theorem blk0 : runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨23, 0, 32, 2 ^ 2048, 256⟩ : ArbEcon.Off.OCfg) 30000 (StO.init (ArbEcon.OrderK.cfg64 1000000 0) 5) = S6 := by
  sorry

end RHX1000000.Run.E41

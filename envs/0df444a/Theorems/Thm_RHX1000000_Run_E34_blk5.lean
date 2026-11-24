-- Prove2me | Theorems.Thm_RHX1000000_Run_E34_blk5
-- name    : RHX1000000.Run.E34.blk5
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T03:59:58.219463+00:00
-- url     : https://prove2.me/theorems/71e27af7-9289-4668-898b-0e93f5f2a2f7
-- title:
--   Evaluator run at the centre of edge piece 34 at height 1000000, block 5
-- statement:
--   The framework's offline Euler–Maclaurin evaluator with the configuration of edge piece 34 at height $10^6$, run for $30000$ steps from the state `S30`, ends in the state `S36` (states from the definitions `RHX1E6_RunE34`).
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000; extended to height 100000 by the RHX100000 problems) to height 1000000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_ArdaRH65K_Turing121_H11K_EdgeSplit
import Definitions.Def_ArdaRS_Config64
import Definitions.Def_RHX1E6_RunE34
import Definitions.Def_RHX_Edge1000000Data
import Definitions.Def_RHX_RunChain
import Definitions.Def_RHX_RunSplit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open ArbEcon.Off

namespace RHX1000000.Run.E34

theorem blk5 : runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨15, 0, 16, 2 ^ 1024, 256⟩ : ArbEcon.Off.OCfg) 30000 S30 = S36 := by
  sorry

end RHX1000000.Run.E34

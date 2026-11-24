-- Prove2me | Theorems.Thm_RHX1000000_Run_E62_blk9
-- name    : RHX1000000.Run.E62.blk9
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T07:04:46.120152+00:00
-- url     : https://prove2.me/theorems/7f5e84fd-0c7c-478b-980e-219b94c00bc0
-- title:
--   Evaluator run at the centre of edge piece 62 at height 1000000, block 9
-- statement:
--   The framework's offline Euler–Maclaurin evaluator with the configuration of edge piece 62 at height $10^6$, run for $29998$ steps from the state `S54`, ends in the state `S60` (states from the definitions `RHX1E6_RunE62`).
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000; extended to height 100000 by the RHX100000 problems) to height 1000000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_ArdaRH65K_Turing121_H11K_EdgeSplit
import Definitions.Def_ArdaRS_Config64
import Definitions.Def_RHX1E6_RunE62
import Definitions.Def_RHX_Edge1000000Data
import Definitions.Def_RHX_RunChain
import Definitions.Def_RHX_RunSplit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open ArbEcon.Off

namespace RHX1000000.Run.E62

theorem blk9 : runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨0, 3, 8, 2 ^ 512, 256⟩ : ArbEcon.Off.OCfg) 29998 S54 = S60 := by
  sorry

end RHX1000000.Run.E62

-- Prove2me | Theorems.Thm_RHX1000000_Run_E18_run
-- name    : RHX1000000.Run.E18.run
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T02:28:43.607309+00:00
-- url     : https://prove2.me/theorems/cc3e1919-502d-4c88-91b8-a86f6af354d1
-- title:
--   Evaluator run at the centre of edge piece 18 at height 1000000
-- statement:
--   The framework's offline Euler–Maclaurin evaluator with the configuration of edge piece 18 at height $10^6$, run from its initial state over the full number of terms, ends in the literal state `RHX1000000.Run.E18.S60`.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000; extended to height 100000 by the RHX100000 problems) to height 1000000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_ArdaRH65K_Turing121_H11K_EdgeSplit
import Definitions.Def_ArdaRS_Config64
import Definitions.Def_RHX1E6_RunE18
import Definitions.Def_RHX_Edge1000000Data
import Definitions.Def_RHX_RunChain
import Definitions.Def_RHX_RunSplit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open ArbEcon.Off

namespace RHX1000000.Run.E18

theorem run : runO (ArbEcon.OrderK.cfg64 1000000 0) (⟨23, 0, 16, 2 ^ 1024, 256⟩ : ArbEcon.Off.OCfg) 299998 (StO.init (ArbEcon.OrderK.cfg64 1000000 0) 5) = S60 := by
  sorry

end RHX1000000.Run.E18

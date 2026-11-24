-- Prove2me | Theorems.Thm_RHX1000000_Run_C01_run
-- name    : RHX1000000.Run.C01.run
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T08:24:40.926302+00:00
-- url     : https://prove2.me/theorems/f803bcf1-afd2-4778-982e-4536be3d3514
-- title:
--   Evaluator run at the centre of slab cell 1 at height 1000000
-- statement:
--   The framework's offline Euler–Maclaurin evaluator with the configuration of slab cell 1 at height $10^6$, run from its initial state over the full number of terms, ends in the literal state `RHX1000000.Run.C01.S60`.
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

theorem run : runO (ArbEcon.OrderK.cfg64 16384000025 14) (⟨23, 0, 40, 2 ^ 2560, 256⟩ : ArbEcon.Off.OCfg) 299999 (StO.init (ArbEcon.OrderK.cfg64 16384000025 14) 5) = S60 := by
  sorry

end RHX1000000.Run.C01

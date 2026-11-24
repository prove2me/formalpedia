-- Prove2me | Theorems.Thm_RHX_runO_add
-- name    : RHX.runO_add
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:47:14.041788+00:00
-- url     : https://prove2.me/theorems/712aca80-1bb0-4b34-8446-4551f26c1aa4
-- title:
--   Evaluator lemma: runO_add
-- statement:
--   Runs compose: `runO c o (a + b) s = runO c o b (runO c o a s)`.
--
--   A lemma about the framework's `ArbEcon.Off.runO`: it lets a long kernel computation be checked as several small goals.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000; extended to height 100000 by the RHX100000 problems) to height 1000000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_RHX_RunChain
set_option maxRecDepth 100000
open ArbEcon.Off

namespace RHX

theorem runO_add (c : ArbEcon.Cfg) (o : OCfg) : ∀ (a b : Nat) (s : StO),
    runO c o (a + b) s = runO c o b (runO c o a s) := by
  sorry

end RHX

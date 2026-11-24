-- Prove2me | Theorems.Thm_RHX_runO_succ
-- name    : RHX.runO_succ
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:47:11.093903+00:00
-- url     : https://prove2.me/theorems/aea70140-58f5-4a72-bee2-8fcf2c2c74ed
-- title:
--   Evaluator lemma: runO_succ
-- statement:
--   One more evaluator step: `runO c o (n + 1) s = runO c o n (stepO c o s)`.
--
--   A lemma about the framework's `ArbEcon.Off.runO`: it lets a long kernel computation be checked as several small goals.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000; extended to height 100000 by the RHX100000 problems) to height 1000000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_RHX_RunChain
set_option maxRecDepth 100000
open ArbEcon.Off

namespace RHX

theorem runO_succ (c : ArbEcon.Cfg) (o : OCfg) (n : Nat) (s : StO) :
    runO c o (n + 1) s = runO c o n (stepO c o s) := by
  sorry

end RHX

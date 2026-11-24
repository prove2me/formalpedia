-- Prove2me | Theorems.Thm_RHX_runO_chain
-- name    : RHX.runO_chain
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:47:16.750948+00:00
-- url     : https://prove2.me/theorems/4a4987dd-afc2-43b0-9de3-2d48491629f5
-- title:
--   Evaluator lemma: runO_chain
-- statement:
--   Two checked chunks chain: from `runO c o a s = t` and `runO c o b t = u` follows `runO c o (a + b) s = u`.
--
--   A lemma about the framework's `ArbEcon.Off.runO`: it lets a long kernel computation be checked as several small goals.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000; extended to height 100000 by the RHX100000 problems) to height 1000000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_RHX_RunChain
set_option maxRecDepth 100000
open ArbEcon.Off

namespace RHX

theorem runO_chain (c : ArbEcon.Cfg) (o : OCfg) {a b : Nat} {s t u : StO}
    (h1 : runO c o a s = t) (h2 : runO c o b t = u) : runO c o (a + b) s = u := by
  sorry

end RHX

-- Prove2me | Theorems.Thm_RHX_stoBeq_eq
-- name    : RHX.stoBeq_eq
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:47:09.30439+00:00
-- url     : https://prove2.me/theorems/4e19bd1e-51e6-401f-b28f-cea87afe7772
-- title:
--   Evaluator lemma: stoBeq_eq
-- statement:
--   `RHX.stoBeq s t = true` implies `s = t` for evaluator states.
--
--   A lemma about the framework's `RHX.stoBeq`: it lets a long kernel computation be checked as several small goals.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000; extended to height 100000 by the RHX100000 problems) to height 1000000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_RHX_RunChain
set_option maxRecDepth 100000
open ArbEcon.Off

namespace RHX

theorem stoBeq_eq {s t : StO} (h : stoBeq s t = true) : s = t := by
  sorry

end RHX

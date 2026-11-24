-- Prove2me | Theorems.Thm_RHX_boxOK_of_run
-- name    : RHX.boxOK_of_run
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:50:56.938639+00:00
-- url     : https://prove2.me/theorems/22beda92-4b0a-41ad-8e32-e1829b696100
-- title:
--   Evaluator lemma: boxOK_of_run
-- statement:
--   `Arb4.boxOK` follows from the run equality for the box centre and `RHX.boxOKs` on its final state.
--
--   A lemma about the framework's `Arb4.boxOK`: it lets a long kernel computation be checked as several small goals.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000; extended to height 100000 by the RHX100000 problems) to height 1000000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_RHX_RunSplit
set_option maxRecDepth 100000
open Arb4 Arb4.Q

namespace RHX

theorem boxOK_of_run (tn tq N : ℕ) (P : PieceD) (D : ℕ) (reLo reHi imLo imHi : ℤ) (Qp Rn Rd : ℕ)
    (qlo qhi : Q) (S : ArbEcon.Off.StO)
    (hrun : ArbEcon.Off.runO (ArbEcon.OrderK.cfg64 tn tq) P.oc (N - 2)
      (ArbEcon.Off.StO.init (ArbEcon.OrderK.cfg64 tn tq) 5) = S)
    (h : boxOKs tn tq N P D reLo reHi imLo imHi Qp Rn Rd qlo qhi S = true) :
    boxOK tn tq N P D reLo reHi imLo imHi Qp Rn Rd qlo qhi = true := by
  sorry

end RHX

-- Prove2me | Theorems.Thm_RHX_pieceOK_of_run
-- name    : RHX.pieceOK_of_run
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:50:55.85316+00:00
-- url     : https://prove2.me/theorems/147ab1cb-0b85-418c-9194-5214fd1f70af
-- title:
--   Evaluator lemma: pieceOK_of_run
-- statement:
--   `Arb4.pieceOK` follows from the run equality for the piece centre and `RHX.pieceOKs` on its final state.
--
--   A lemma about the framework's `Arb4.pieceOK`: it lets a long kernel computation be checked as several small goals.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000; extended to height 100000 by the RHX100000 problems) to height 1000000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_RHX_RunSplit
set_option maxRecDepth 100000
open Arb4 Arb4.Q

namespace RHX

theorem pieceOK_of_run (tn tq N : ℕ) (L : Q) (P : PieceD) (S : ArbEcon.Off.StO)
    (hrun : ArbEcon.Off.runO (ArbEcon.OrderK.cfg64 tn tq) P.oc (N - 2)
      (ArbEcon.Off.StO.init (ArbEcon.OrderK.cfg64 tn tq) 5) = S)
    (h : pieceOKs tn tq N L P S = true) : pieceOK tn tq N L P = true := by
  sorry

end RHX

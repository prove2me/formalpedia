-- Prove2me | Theorems.Thm_RHX_cellOK_of_run
-- name    : RHX.cellOK_of_run
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T00:50:58.955308+00:00
-- url     : https://prove2.me/theorems/fd63e223-d7aa-4341-b947-7b310168873a
-- title:
--   Evaluator lemma: cellOK_of_run
-- statement:
--   `Arb4.cellOK` follows from the run equality for the cell centre and `RHX.cellOKs` on its final state.
--
--   A lemma about the framework's `Arb4.cellOK`: it lets a long kernel computation be checked as several small goals.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000; extended to height 100000 by the RHX100000 problems) to height 1000000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_RHX_RunSplit
set_option maxRecDepth 100000
open Arb4 Arb4.Q

namespace RHX

theorem cellOK_of_run (S : SlabD) (j : ℕ) (St : ArbEcon.Off.StO)
    (hrun : ArbEcon.Off.runO (ArbEcon.OrderK.cfg64 (S.cell j).tn S.tq) (S.cell j).oc (S.N - 2)
      (ArbEcon.Off.StO.init (ArbEcon.OrderK.cfg64 (S.cell j).tn S.tq) 5) = St)
    (h : cellOKs S j St = true) : cellOK S j = true := by
  sorry

end RHX

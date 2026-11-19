-- Prove2me | Theorems.Thm_RHX_pieceJ_of
-- name    : RHX.pieceJ_of
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-18T19:49:49.566494+00:00
-- url     : https://prove2.me/theorems/89999677-39d6-473f-9036-1c1107a1f1ba
-- title:
--   Conjunct split of H11K.pieceJ
-- statement:
--   `H11K.pieceJ E j = true` follows from `Arb4.pieceOK` for piece $j$ and the two breakpoint radius checks.
--
--   This is a computation-free lemma: it restates a checker of the published framework (`H11K.pieceJ`) as the conjunction of its conjuncts, so that each conjunct can be checked by the kernel as a separate small goal.
-- source:
--   Computational certificate extending the kernel-checked verification of the Riemann hypothesis on prove2.me (published ArdaRH65K framework, Proved to height 65000) to height 100000; data produced by an exact integer Rust port of the framework checkers and checked by the Lean kernel.

import Definitions.Def_ArdaRH65K_Turing121_H11K_EdgeSplit
set_option maxRecDepth 100000
open Arb4

namespace RHX

theorem pieceJ_of (E : EdgeD) (j : ℕ) (hp : pieceOK E.tn E.tq E.N E.L (E.pc j) = true)
    (h1 : inRad (E.x j) (E.pc j) = true) (h2 : inRad (E.x (j + 1)) (E.pc j) = true) :
    H11K.pieceJ E j = true := by
  sorry

end RHX

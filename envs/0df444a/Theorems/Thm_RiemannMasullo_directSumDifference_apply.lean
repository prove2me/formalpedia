-- Prove2me | Theorems.Thm_RiemannMasullo_directSumDifference_apply
-- name    : RiemannMasullo.directSumDifference_apply
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:37:45.152332+00:00
-- url     : https://prove2.me/theorems/d71021f4-776e-42bb-895a-a2559183b5b3
-- title:
--   Coordinates of the inductive-system difference operator
-- statement:
--   On the algebraic direct sum the difference operator fixes coordinate zero. In coordinate k+1 it subtracts the transition map applied to coordinate k from coordinate k+1.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec1.lean#L437-L460

import Definitions.Def_RiemannMasullo_AppC_InductiveLimits

open RiemannMasullo
open Set Filter Topology TopologicalSpace Bornology
open scoped Pointwise DirectSum
variable {E : Type*} [AddCommGroup E] [Module ℂ E] [tE : TopologicalSpace E]
variable {X : ℕ → Type*} [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
  [∀ k, TopologicalSpace (X k)]

namespace RiemannMasullo

theorem directSumDifference_apply (j : ∀ k, X k →L[ℂ] X (k+1)) (x : ⨁ k, X k) :
    directSumDifference j x 0 = x 0 ∧
      ∀ k, directSumDifference j x (k+1) = x (k+1) - j k (x k) := by sorry

end RiemannMasullo

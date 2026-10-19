-- Prove2me | Theorems.Thm_SoficGroups_KunCompletedProductDiagonalSparseCut_completedGoodPermutationGraphRootedModel_isRootedAtRadius
-- name    : SoficGroups.KunCompletedProductDiagonalSparseCut.completedGoodPermutationGraphRootedModel_isRootedAtRadius
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/060c98a9-7b50-429e-95f6-11628ab442e6
-- title:
--   SoficGroups.KunCompletedProductDiagonalSparseCut.completedGoodPermutationGraphRootedModel_isRootedAtRadius
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCompletedProductDiagonalSparseCut
open SoficGroups.KunDiagonalGoodRootGraphLoss
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunRootedWordPower
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators symmDiff
universe u

theorem SoficGroups.KunCompletedProductDiagonalSparseCut.completedGoodPermutationGraphRootedModel_isRootedAtRadius
    {G ι V : Type u} [Group G]
    [Fintype V] [DecidableEq V]
    (w : G → List ι) (σ : ι → Equiv.Perm V)
    (φ : G → Equiv.Perm V)
    (p : Equiv.Perm V) (B : Finset V) (r : ℕ)
    (hroot : ∀ a g : G,
      (w a).length + (w g).length + (w (a * g)).length ≤ r →
        ∀ x : V, x ∉ B →
          φ (a * g) x = (φ a * φ g) x) :
    (completedGoodPermutationGraphRootedModel
      σ φ p B).IsRootedAtRadius w r := by sorry

-- Prove2me | Theorems.Thm_SoficGroups_KunCompletedProductDiagonalSparseCut_completedGoodPermutationGraphRootedModel_isGenerated
-- name    : SoficGroups.KunCompletedProductDiagonalSparseCut.completedGoodPermutationGraphRootedModel_isGenerated
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/6c1739bc-734c-406f-94ed-2eeea9e21c3f
-- title:
--   SoficGroups.KunCompletedProductDiagonalSparseCut.completedGoodPermutationGraphRootedModel_isGenerated
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

theorem SoficGroups.KunCompletedProductDiagonalSparseCut.completedGoodPermutationGraphRootedModel_isGenerated
    {G ι V : Type u} [Group G] [Fintype ι]
    [Fintype V] [DecidableEq V]
    (s : ι → G) (w : G → List ι)
    (σ : ι → Equiv.Perm V) (φ : G → Equiv.Perm V)
    (hword : ∀ g : G, φ g = ((w g).map σ).prod)
    (hone : φ 1 = 1)
    (hgenerator : ∀ i : ι, φ (s i) = σ i)
    (p : Equiv.Perm V) (B : Finset V) :
    (completedGoodPermutationGraphRootedModel σ φ p B).IsGenerated s w := by sorry

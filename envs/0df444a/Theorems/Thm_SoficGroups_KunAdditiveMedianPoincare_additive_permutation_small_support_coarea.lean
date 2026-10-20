-- Prove2me | Theorems.Thm_SoficGroups_KunAdditiveMedianPoincare_additive_permutation_small_support_coarea
-- name    : SoficGroups.KunAdditiveMedianPoincare.additive_permutation_small_support_coarea
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/babde6ac-0186-479f-aca2-1c0ec6cb387f
-- title:
--   SoficGroups.KunAdditiveMedianPoincare.additive_permutation_small_support_coarea
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunAdditiveMedianPoincare
open SoficGroups.CheegerPoincare
open Filter Topology
open scoped BigOperators

theorem SoficGroups.KunAdditiveMedianPoincare.additive_permutation_small_support_coarea
    {V ι : Type*} [Fintype V]
    [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (γ ε : ℝ)
    (hε : 0 ≤ ε)
    (hexp : ∀ A : Finset V,
      γ * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (SoficGroups.boundary σ A : ℝ) + ε)
    (f : V → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ x, 0 ≤ f x)
    (hfM : ∀ x, f x ≤ M)
    (hhalf :
      2 * (SoficGroups.CheegerPoincare.positiveSupport f).card ≤
        Fintype.card V) :
    2 * γ * (∑ x : V, f x) ≤
      permutationRealVariation σ f + 2 * ε * M := by sorry

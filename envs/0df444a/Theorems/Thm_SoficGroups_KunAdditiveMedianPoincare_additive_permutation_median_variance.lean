-- Prove2me | Theorems.Thm_SoficGroups_KunAdditiveMedianPoincare_additive_permutation_median_variance
-- name    : SoficGroups.KunAdditiveMedianPoincare.additive_permutation_median_variance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/aa5cca2b-1b2f-4384-8350-3ad2c6adf6c7
-- title:
--   SoficGroups.KunAdditiveMedianPoincare.additive_permutation_median_variance
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

theorem SoficGroups.KunAdditiveMedianPoincare.additive_permutation_median_variance
    {V ι : Type*} [Fintype V] [Nonempty V]
    [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (γ ε : ℝ)
    (hγ : 0 ≤ γ)
    (hε : 0 ≤ ε)
    (hexp : ∀ A : Finset V,
      γ * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (SoficGroups.boundary σ A : ℝ) + ε)
    (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x)
    (hf_one : ∀ x, f x ≤ 1) :
    2 * γ *
        (∑ x : V,
          (f x - SoficGroups.CheegerPoincare.finiteMean f) ^ 2) ≤
      permutationRealVariation σ f + 4 * ε := by sorry

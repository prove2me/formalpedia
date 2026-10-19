-- Prove2me | Theorems.Thm_SoficGroups_KunAdditiveMedianPoincare_permutationRealVariation_positive_negative
-- name    : SoficGroups.KunAdditiveMedianPoincare.permutationRealVariation_positive_negative
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/ae98a0d5-91c8-44f3-97de-be2e1f8d6ac2
-- title:
--   SoficGroups.KunAdditiveMedianPoincare.permutationRealVariation_positive_negative
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

theorem SoficGroups.KunAdditiveMedianPoincare.permutationRealVariation_positive_negative
    {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (m : ℝ) :
    permutationRealVariation σ (fun x => max (f x - m) 0) +
      permutationRealVariation σ (fun x => max (m - f x) 0) =
        permutationRealVariation σ f := by sorry

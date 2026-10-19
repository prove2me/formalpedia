-- Prove2me | Theorems.Thm_SoficGroups_KunActualFinalRestrictedVariation_sum_sum_sq_displacement_le_twice_card_mul_sqrt_card_mul_residual
-- name    : SoficGroups.KunActualFinalRestrictedVariation.sum_sum_sq_displacement_le_twice_card_mul_sqrt_card_mul_residual
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/6ba5939c-b5ef-4abd-9236-e9634782ac5a
-- title:
--   SoficGroups.KunActualFinalRestrictedVariation.sum_sum_sq_displacement_le_twice_card_mul_sqrt_card_mul_residual
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFinalRestrictedVariation
open scoped BigOperators

theorem SoficGroups.KunActualFinalRestrictedVariation.sum_sum_sq_displacement_le_twice_card_mul_sqrt_card_mul_residual
    {V ι : Type*} [Fintype V]
    [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (T : Finset V) (f : V → ℝ)
    (hfzero : ∀ x, 0 ≤ f x) (hfone : ∀ x, f x ≤ 1)
    (hmass : (∑ x : V, f x) = (T.card : ℝ)) :
    (∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2) ≤
      2 * (Fintype.card ι : ℝ) * Real.sqrt (T.card : ℝ) *
        Real.sqrt (∑ x : V,
          (realMarkov σ f x - f x) ^ 2) := by sorry

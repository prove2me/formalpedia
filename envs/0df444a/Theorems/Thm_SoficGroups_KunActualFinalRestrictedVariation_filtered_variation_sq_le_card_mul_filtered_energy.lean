-- Prove2me | Theorems.Thm_SoficGroups_KunActualFinalRestrictedVariation_filtered_variation_sq_le_card_mul_filtered_energy
-- name    : SoficGroups.KunActualFinalRestrictedVariation.filtered_variation_sq_le_card_mul_filtered_energy
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/a2ed4919-d179-4be1-8001-80dc0aef6384
-- title:
--   SoficGroups.KunActualFinalRestrictedVariation.filtered_variation_sq_le_card_mul_filtered_energy
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFinalRestrictedVariation
open scoped BigOperators

theorem SoficGroups.KunActualFinalRestrictedVariation.filtered_variation_sq_le_card_mul_filtered_energy
    {V ι : Type*} [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (H : Finset V) :
    (∑ i : ι, ∑ x ∈ H, |f (σ i x) - f x|) ^ 2 ≤
      (Fintype.card ι : ℝ) * (H.card : ℝ) *
        ∑ i : ι, ∑ x ∈ H, (f (σ i x) - f x) ^ 2 := by sorry

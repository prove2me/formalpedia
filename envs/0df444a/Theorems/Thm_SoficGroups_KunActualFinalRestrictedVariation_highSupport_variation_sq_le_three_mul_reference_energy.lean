-- Prove2me | Theorems.Thm_SoficGroups_KunActualFinalRestrictedVariation_highSupport_variation_sq_le_three_mul_reference_energy
-- name    : SoficGroups.KunActualFinalRestrictedVariation.highSupport_variation_sq_le_three_mul_reference_energy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/2a7a4b2e-d7ed-4b86-8fbf-2c86dc5ee619
-- title:
--   SoficGroups.KunActualFinalRestrictedVariation.highSupport_variation_sq_le_three_mul_reference_energy
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFinalRestrictedVariation
open scoped BigOperators

theorem SoficGroups.KunActualFinalRestrictedVariation.highSupport_variation_sq_le_three_mul_reference_energy
    {V ι : Type*} [Fintype V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (T : Finset V)
    (hhigh :
      ((Finset.univ.filter
        (fun x : V => (1 / 3 : ℝ) < f x)).card : ℝ) ≤
          3 * (T.card : ℝ)) :
    (∑ i : ι,
      ∑ x ∈ Finset.univ.filter
        (fun x : V => (1 / 3 : ℝ) < f x),
          |f (σ i x) - f x|) ^ 2 ≤
      3 * (Fintype.card ι : ℝ) * (T.card : ℝ) *
        ∑ i : ι, ∑ x : V, (f (σ i x) - f x) ^ 2 := by sorry

-- Prove2me | Theorems.Thm_SoficGroups_KunActualFinalRestrictedVariation_sum_sq_displacement_eq_twice_inverse_residual
-- name    : SoficGroups.KunActualFinalRestrictedVariation.sum_sq_displacement_eq_twice_inverse_residual
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/de72e2f2-7486-4865-9d63-469843583293
-- title:
--   SoficGroups.KunActualFinalRestrictedVariation.sum_sq_displacement_eq_twice_inverse_residual
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFinalRestrictedVariation
open scoped BigOperators

theorem SoficGroups.KunActualFinalRestrictedVariation.sum_sq_displacement_eq_twice_inverse_residual
    {V : Type*} [Fintype V]
    (p : Equiv.Perm V) (f : V → ℝ) :
    (∑ x : V, (f (p x) - f x) ^ 2) =
      2 * ∑ x : V, f x * (f x - f (p.symm x)) := by sorry

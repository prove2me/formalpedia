-- Prove2me | Theorems.Thm_SoficGroups_KunActualFinalRestrictedVariation_sum_permutation_mul_eq_sum_inverse_mul
-- name    : SoficGroups.KunActualFinalRestrictedVariation.sum_permutation_mul_eq_sum_inverse_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/1a10ec72-1997-4221-ae14-543a79a60693
-- title:
--   SoficGroups.KunActualFinalRestrictedVariation.sum_permutation_mul_eq_sum_inverse_mul
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualFinalRestrictedVariation
open scoped BigOperators

theorem SoficGroups.KunActualFinalRestrictedVariation.sum_permutation_mul_eq_sum_inverse_mul
    {V : Type*} [Fintype V]
    (p : Equiv.Perm V) (f : V → ℝ) :
    (∑ x : V, f (p x) * f x) =
      ∑ x : V, f x * f (p.symm x) := by sorry

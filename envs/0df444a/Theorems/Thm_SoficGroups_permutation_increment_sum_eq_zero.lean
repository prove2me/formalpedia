-- Prove2me | Theorems.Thm_SoficGroups_permutation_increment_sum_eq_zero
-- name    : SoficGroups.permutation_increment_sum_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.258421+00:00
-- url     : https://prove2.me/theorems/3f1ace7d-96ef-4f6c-89fd-e63b610661b3
-- title:
--   SoficGroups.permutation_increment_sum_eq_zero
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff

theorem SoficGroups.permutation_increment_sum_eq_zero
    {α : Type*} [Fintype α] (p : Equiv.Perm α) (f : α → ℝ) :
    ∑ x, (f (p x) - f x) = 0 := by sorry

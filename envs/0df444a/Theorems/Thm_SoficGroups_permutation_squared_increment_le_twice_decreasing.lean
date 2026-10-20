-- Prove2me | Theorems.Thm_SoficGroups_permutation_squared_increment_le_twice_decreasing
-- name    : SoficGroups.permutation_squared_increment_le_twice_decreasing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.258421+00:00
-- url     : https://prove2.me/theorems/7afa3d4e-05da-4d3d-99b1-5c07ac3886e5
-- title:
--   SoficGroups.permutation_squared_increment_le_twice_decreasing
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

theorem SoficGroups.permutation_squared_increment_le_twice_decreasing
    {α : Type*} [Fintype α] (p : Equiv.Perm α) (f : α → ℝ)
    (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_le_one : ∀ x, f x ≤ 1) :
    ∑ x, (f (p x) - f x) ^ 2 ≤
      2 * ((Finset.univ.filter fun x => f (p x) < f x).card : ℝ) := by sorry

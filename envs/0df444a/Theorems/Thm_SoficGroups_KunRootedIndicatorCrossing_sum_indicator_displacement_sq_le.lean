-- Prove2me | Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_sum_indicator_displacement_sq_le
-- name    : SoficGroups.KunRootedIndicatorCrossing.sum_indicator_displacement_sq_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:24.345557+00:00
-- url     : https://prove2.me/theorems/a809c0c4-ed52-4c8a-ab9e-d2c701b3c7c1
-- title:
--   SoficGroups.KunRootedIndicatorCrossing.sum_indicator_displacement_sq_le
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology

theorem SoficGroups.KunRootedIndicatorCrossing.sum_indicator_displacement_sq_le
    {ι V : Type*} [Fintype ι] (p : ι → V → V) (f : V → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1) (x : V) :
    (∑ i, (f (p i x) - f x) ^ 2) ≤
      (∑ i, (f (p i x) - f x)) ^ 2 := by sorry

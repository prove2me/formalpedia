-- Prove2me | Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_sum_sq_le_sq_sum_of_same_sign
-- name    : SoficGroups.KunRootedIndicatorCrossing.sum_sq_le_sq_sum_of_same_sign
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:24.345557+00:00
-- url     : https://prove2.me/theorems/f2d1812f-6c2b-44e0-a62a-0d31b6b51d03
-- title:
--   SoficGroups.KunRootedIndicatorCrossing.sum_sq_le_sq_sum_of_same_sign
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

theorem SoficGroups.KunRootedIndicatorCrossing.sum_sq_le_sq_sum_of_same_sign
    {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (h : (∀ i, 0 ≤ a i) ∨ (∀ i, a i ≤ 0)) :
    (∑ i, a i ^ 2) ≤ (∑ i, a i) ^ 2 := by sorry

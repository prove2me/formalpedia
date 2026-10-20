-- Prove2me | Theorems.Thm_SoficGroups_KunDirectedIndicatorJensen_realPermutationMarkov_sub_sq_le_average_sq
-- name    : SoficGroups.KunDirectedIndicatorJensen.realPermutationMarkov_sub_sq_le_average_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:26.206993+00:00
-- url     : https://prove2.me/theorems/771ce63a-151c-4056-ae53-3f318c24bde6
-- title:
--   SoficGroups.KunDirectedIndicatorJensen.realPermutationMarkov_sub_sq_le_average_sq
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunDirectedIndicatorJensen
open scoped BigOperators

theorem SoficGroups.KunDirectedIndicatorJensen.realPermutationMarkov_sub_sq_le_average_sq
    {V ι : Type*} [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (f : V → ℝ) (x : V) :
    (realPermutationMarkov σ f x - f x) ^ 2 ≤
      (∑ i : ι,
        (f ((σ i).symm x) - f x) ^ 2) /
        (Fintype.card ι : ℝ) := by sorry

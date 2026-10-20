-- Prove2me | Theorems.Thm_SoficGroups_KunDirectedIndicatorJensen_realPermutationMarkov_indicator_defect_sq_le_boundary
-- name    : SoficGroups.KunDirectedIndicatorJensen.realPermutationMarkov_indicator_defect_sq_le_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:26.206993+00:00
-- url     : https://prove2.me/theorems/8d59c439-66b3-4150-b055-e1f10092c7b7
-- title:
--   SoficGroups.KunDirectedIndicatorJensen.realPermutationMarkov_indicator_defect_sq_le_boundary
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunDirectedIndicatorJensen
open scoped BigOperators

theorem SoficGroups.KunDirectedIndicatorJensen.realPermutationMarkov_indicator_defect_sq_le_boundary
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (T : Finset V) :
    (∑ x : V,
      (realPermutationMarkov σ (realIndicator T) x -
        realIndicator T x) ^ 2) ≤
      2 * (SoficGroups.boundary σ T : ℝ) /
        (Fintype.card ι : ℝ) := by sorry

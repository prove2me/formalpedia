-- Prove2me | Theorems.Thm_SoficGroups_ComponentMidrankVariance_sum_weighted_ordered_midpoints_sq
-- name    : SoficGroups.ComponentMidrankVariance.sum_weighted_ordered_midpoints_sq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/7d62b7a1-cdc9-4039-a708-74b215db8603
-- title:
--   SoficGroups.ComponentMidrankVariance.sum_weighted_ordered_midpoints_sq
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
open SoficGroups.ComponentMidrankVariance
open scoped BigOperators

theorem SoficGroups.ComponentMidrankVariance.sum_weighted_ordered_midpoints_sq (s : Finset ℤ) (w : ℤ → ℝ) :
    (∑ j ∈ s, w j * (lowerRankWeight s w j + w j / 2) ^ 2) =
      (∑ j ∈ s, w j) ^ 3 / 3 -
        (∑ j ∈ s, w j ^ 3) / 12 := by sorry

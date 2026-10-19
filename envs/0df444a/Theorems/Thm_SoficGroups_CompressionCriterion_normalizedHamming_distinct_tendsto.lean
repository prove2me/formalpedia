-- Prove2me | Theorems.Thm_SoficGroups_CompressionCriterion_normalizedHamming_distinct_tendsto
-- name    : SoficGroups.CompressionCriterion.normalizedHamming_distinct_tendsto
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.748479+00:00
-- url     : https://prove2.me/theorems/f8464e09-8dc6-41d6-86d9-47623be19875
-- title:
--   SoficGroups.CompressionCriterion.normalizedHamming_distinct_tendsto
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
universe u₁ u₂ u₃
open SoficGroups.CompressionCriterion
open Filter Topology

theorem SoficGroups.CompressionCriterion.normalizedHamming_distinct_tendsto
    {G : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G)
    {g h : G} (hne : g ≠ h) :
    Tendsto
      (fun n => SoficGroups.normalizedHamming
        ((A.model n).action g) ((A.model n).action h))
      atTop (𝓝 1) := by sorry

-- Prove2me | Theorems.Thm_SoficGroups_CanonicalProductRadiusBadMatchedCapture_composite_mem_sourceProductRadiusLabels
-- name    : SoficGroups.CanonicalProductRadiusBadMatchedCapture.composite_mem_sourceProductRadiusLabels
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:31.712996+00:00
-- url     : https://prove2.me/theorems/15f9a9d5-38e7-4449-ad0b-cd727290b1ea
-- title:
--   SoficGroups.CanonicalProductRadiusBadMatchedCapture.composite_mem_sourceProductRadiusLabels
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
open Filter Topology
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.ChosenCayleyMatchedComponentRealization
open SoficGroups.MatchedComponentCompletion
open SoficGroups.MatchedComponentExitBudget
open scoped BigOperators Pointwise symmDiff

theorem SoficGroups.CanonicalProductRadiusBadMatchedCapture.composite_mem_sourceProductRadiusLabels
    {K J : Type*} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (S : Finset K) (F : Finset J) (k : ℕ)
    {a : K} (ha : a ∈ S)
    {j : J}
    (hj : j ∈ SoficGroups.CompressionCriterion.productTrackedTable F) :
    (a, j) ∈ sourceProductRadiusLabels S F k := by sorry

-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPartitionCount_edge_mass_lower
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPartitionCount.edge_mass_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:20:37.772451+00:00
-- url     : https://prove2.me/theorems/ba38fcf1-1396-4b48-be40-1b1967417a73
-- title:
--   edge_mass_lower
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPartitionCount.lean#L253-L265
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryPartitionCount.lean#L253-L265

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_TernaryCoverPartitionLower
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalLocalParameters
import Mathlib.Tactic
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPartitionCount
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPartitionCount
open Finset TernaryJointType TernaryCoverLocal TernaryCoverRegularity TernaryCoverOutputCap
open TernaryTypeLowerBound

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalPartitionCount.edge_mass_lower (t r s : ℕ) :
    (vertices (t+2*r+3*s) (piType t r s)).card*(2^(2*r)*3^(3*s)) ≤
    partitionLoss r s*Fintype.card
      (LocalEdge (t+2*r+3*s) (alphaType t r s) (piType t r s)) := by sorry

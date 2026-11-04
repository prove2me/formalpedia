-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPartitionCount_output_group_mul_vertices_le_edges
-- name    : ThreeSum.WeightedGlobalPartitionCount.output_group_mul_vertices_le_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:58:12.50152+00:00
-- url     : https://prove2.me/theorems/1adf6ea6-dbaf-4fa4-b27e-d915a9e9b4bc
-- title:
--   Weighted Global Partition Count: output group mul vertices le edges
-- statement:
--   The Weighted Global Partition Count construction uses the output group mul vertices le edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPartitionCount.lean#L233-L250
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPartitionCount.lean#L233-L250

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_TernaryCoverPartitionLower
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
import Mathlib.Tactic
import Definitions.Def_Submission_Weighted_Global_TernaryPartitionCount
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPartitionCount
open Finset TernaryJointType TernaryCoverLocal TernaryCoverRegularity TernaryCoverOutputCap
open TernaryTypeLowerBound

theorem ThreeSum.WeightedGlobalPartitionCount.output_group_mul_vertices_le_edges (t r s : ℕ) :
    (vertices (t+2*r+3*s) (piType t r s)).card*partitionGroup r s ≤
    Fintype.card (LocalEdge (t+2*r+3*s) (alphaType t r s) (piType t r s)) := by sorry

-- Prove2me | Theorems.Thm_ThreeSum_TernaryPartitionCount_output_group_mul_vertices_le_edges
-- name    : ThreeSum.TernaryPartitionCount.output_group_mul_vertices_le_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:49:18.481621+00:00
-- url     : https://prove2.me/theorems/629bae7e-0329-4273-932f-f9768e22c798
-- title:
--   Ternary Partition Count: output group mul vertices le edges
-- statement:
--   The Ternary Partition Count construction uses the output group mul vertices le edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartitionCount.lean#L226-L243
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartitionCount.lean#L226-L243

import Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_TernaryCoverPartitionLower
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPartitionCount
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPartitionCount
open Finset TernaryJointType TernaryCoverLocal TernaryCoverRegularity TernaryCoverOutputCap
open TernaryTypeLowerBound

theorem ThreeSum.TernaryPartitionCount.output_group_mul_vertices_le_edges (t r s : ℕ) :
    (vertices (t+2*r+3*s) (piType t r s)).card*partitionGroup r s ≤
    Fintype.card (LocalEdge (t+2*r+3*s) (alphaType t r s) (piType t r s)) := by sorry

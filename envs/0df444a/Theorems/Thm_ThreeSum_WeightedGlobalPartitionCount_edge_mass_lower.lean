-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPartitionCount_edge_mass_lower
-- name    : ThreeSum.WeightedGlobalPartitionCount.edge_mass_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:58:09.740275+00:00
-- url     : https://prove2.me/theorems/31d1ebaa-0526-42d8-a46a-083cf55b6bb4
-- title:
--   Weighted Global Partition Count: edge mass lower
-- statement:
--   The actual graph edge mass pays the full partition cap up to a polynomial.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPartitionCount.lean#L253-L265
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPartitionCount.lean#L253-L265

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

theorem ThreeSum.WeightedGlobalPartitionCount.edge_mass_lower (t r s : ℕ) :
    (vertices (t+2*r+3*s) (piType t r s)).card*(2^(2*r)*3^(3*s)) ≤
    partitionLoss r s*Fintype.card
      (LocalEdge (t+2*r+3*s) (alphaType t r s) (piType t r s)) := by sorry

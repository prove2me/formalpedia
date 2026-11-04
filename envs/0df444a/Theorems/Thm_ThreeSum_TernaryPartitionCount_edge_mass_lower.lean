-- Prove2me | Theorems.Thm_ThreeSum_TernaryPartitionCount_edge_mass_lower
-- name    : ThreeSum.TernaryPartitionCount.edge_mass_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:49:59.223941+00:00
-- url     : https://prove2.me/theorems/c747b1d7-1c8a-43b2-b72c-cae2b55047f2
-- title:
--   Ternary Partition Count: edge mass lower
-- statement:
--   The actual graph edge mass pays the full partition cap up to a polynomial.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartitionCount.lean#L246-L258
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartitionCount.lean#L246-L258

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

theorem ThreeSum.TernaryPartitionCount.edge_mass_lower (t r s : ℕ) :
    (vertices (t+2*r+3*s) (piType t r s)).card*(2^(2*r)*3^(3*s)) ≤
    partitionLoss r s*Fintype.card
      (LocalEdge (t+2*r+3*s) (alphaType t r s) (piType t r s)) := by sorry

-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPartitionCount_fixed_edge_mass_lower
-- name    : ThreeSum.WeightedGlobalPartitionCount.fixed_edge_mass_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:27:17.39722+00:00
-- url     : https://prove2.me/theorems/39b795b1-f9f9-4828-b65f-e26a8f03f9d8
-- title:
--   Weighted Global Partition Count: fixed edge mass lower
-- statement:
--   The Weighted Global Partition Count construction uses the fixed edge mass lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPartitionCount.lean#L269-L285
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPartitionCount.lean#L269-L285

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
open WeightedGlobalLocalParameters

theorem ThreeSum.WeightedGlobalPartitionCount.fixed_edge_mass_lower (m : ℕ) :
    (vertices (fixedLength m) (fixedPi m)).card*(2^(fixedPi m 1)*3^(fixedPi m 2)) ≤
    partitionLoss (2380004124000*m) (292746547000*m)*
      Fintype.card (LocalEdge (fixedLength m) (fixedAlpha m) (fixedPi m)) := by sorry

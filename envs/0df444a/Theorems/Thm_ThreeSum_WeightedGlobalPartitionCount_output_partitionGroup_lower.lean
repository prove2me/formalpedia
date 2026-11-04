-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPartitionCount_output_partitionGroup_lower
-- name    : ThreeSum.WeightedGlobalPartitionCount.output_partitionGroup_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:00:46.160512+00:00
-- url     : https://prove2.me/theorems/3effee7a-ba74-4a41-b4ca-9de118c89f5d
-- title:
--   Weighted Global Partition Count: output partition Group lower
-- statement:
--   The Weighted Global Partition Count construction uses the output partition Group lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPartitionCount.lean#L225-L231
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPartitionCount.lean#L225-L231

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

theorem ThreeSum.WeightedGlobalPartitionCount.output_partitionGroup_lower (t r s : ℕ) (q : TritWord (t+2*r+3*s))
    (hq : HasType q (piType t r s)) :
    partitionGroup r s ≤ Fintype.card (outputFiber (alphaType t r s) (piType t r s) q) := by sorry

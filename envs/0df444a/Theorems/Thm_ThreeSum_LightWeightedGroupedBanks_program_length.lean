-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGroupedBanks_program_length
-- name    : ThreeSum.LightWeightedGroupedBanks.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:13:00.237013+00:00
-- url     : https://prove2.me/theorems/45fbfd50-bd7d-4e28-8c93-05319e63e39a
-- title:
--   Light Weighted Grouped Banks: program length
-- statement:
--   The Light Weighted Grouped Banks construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GroupedBanks.lean#L28-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GroupedBanks.lean#L28-L28

import Definitions.Def_Submission_Weighted_GroupBankStep
import Definitions.Def_Submission_Weighted_GroupedBanks
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightWeightedBankStages_program_length
import Theorems.Thm_ThreeSum_LightWeightedGroupBankStep_program_length
attribute [local simp] ThreeSum.LightWeightedBankAssembly.program_length
attribute [local simp] ThreeSum.LightWeightedBankStages.program_length


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGroupedBanks
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.LightWeightedBankSweep
set_option maxHeartbeats 6000000
variable {lim : Limits}

theorem ThreeSum.LightWeightedGroupedBanks.program_length : program.length=20 := by sorry

attribute [defeq] ThreeSum.LightWeightedGroupedBanks.program_length

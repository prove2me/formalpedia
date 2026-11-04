-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGroupBankStep_program_length
-- name    : ThreeSum.LightWeightedGroupBankStep.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:04:45.362939+00:00
-- url     : https://prove2.me/theorems/b8a62f12-0a6e-4793-bdb4-ba4e27ae5f41
-- title:
--   Light Weighted Group Bank Step: program length
-- statement:
--   The Light Weighted Group Bank Step construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GroupBankStep.lean#L93-L93
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GroupBankStep.lean#L93-L93

import Definitions.Def_Submission_Weighted_BankResources
import Definitions.Def_Submission_Weighted_GroupBankStep
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightWeightedBankStages_program_length
attribute [local simp] ThreeSum.LightWeightedBankAssembly.program_length
attribute [local simp] ThreeSum.LightWeightedBankStages.program_length


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGroupBankStep
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.LightWeightedBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits}

theorem ThreeSum.LightWeightedGroupBankStep.program_length : program.length=19 := by sorry

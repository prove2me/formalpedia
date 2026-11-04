-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryGroupBankStep_program_length
-- name    : ThreeSum.LightTernaryGroupBankStep.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:06:33.043822+00:00
-- url     : https://prove2.me/theorems/43860f6a-3219-451d-b176-0077e65cc98d
-- title:
--   Light Ternary Group Bank Step: program length
-- statement:
--   The Light Ternary Group Bank Step construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryGroupBankStep.lean#L88-L88
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryGroupBankStep.lean#L88-L88

import Definitions.Def_Submission_ThreeSum_LightTernaryBankResources
import Definitions.Def_Submission_ThreeSum_LightTernaryGroupBankStep
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightTernaryBankStages_program_length
attribute [local simp] ThreeSum.LightTernaryBankAssembly.program_length
attribute [local simp] ThreeSum.LightTernaryBankStages.program_length


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryGroupBankStep
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.LightTernaryBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits}

theorem ThreeSum.LightTernaryGroupBankStep.program_length : program.length=19 := by sorry

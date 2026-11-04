-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryGroupedBanks_program_length
-- name    : ThreeSum.LightTernaryGroupedBanks.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:14:16.841429+00:00
-- url     : https://prove2.me/theorems/fc225ec2-cb05-4e4f-99f5-4a2ca257544c
-- title:
--   Light Ternary Grouped Banks: program length
-- statement:
--   The Light Ternary Grouped Banks construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryGroupedBanks.lean#L23-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryGroupedBanks.lean#L23-L23

import Definitions.Def_Submission_ThreeSum_LightTernaryGroupBankStep
import Definitions.Def_Submission_ThreeSum_LightTernaryGroupedBanks
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightTernaryBankStages_program_length
import Theorems.Thm_ThreeSum_LightTernaryGroupBankStep_program_length
attribute [local simp] ThreeSum.LightTernaryBankAssembly.program_length
attribute [local simp] ThreeSum.LightTernaryBankStages.program_length


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryGroupedBanks
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.LightTernaryBankSweep
set_option maxHeartbeats 6000000
variable {lim : Limits}

theorem ThreeSum.LightTernaryGroupedBanks.program_length : program.length=20 := by sorry

attribute [defeq] ThreeSum.LightTernaryGroupedBanks.program_length

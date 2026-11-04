-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedBankAssembly_program_length
-- name    : ThreeSum.LightWeightedBankAssembly.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:56:56.636198+00:00
-- url     : https://prove2.me/theorems/55103c73-ea4d-4445-8a43-aec67af5af80
-- title:
--   Light Weighted Bank Assembly: program length
-- statement:
--   The Light Weighted Bank Assembly construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankAssembly.lean#L42-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankAssembly.lean#L42-L42

import Definitions.Def_Submission_Weighted_BankStages
import Definitions.Def_Submission_ThreeSum_LightTernaryProduct
import Definitions.Def_Submission_Weighted_BankAssembly
import Theorems.Thm_ThreeSum_LightWeightedBankStages_program_length
attribute [local simp] ThreeSum.LightWeightedBankStages.program_length


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedBankAssembly
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightWeightedBankSweep
set_option maxHeartbeats 6000000
variable {lim : Limits}

theorem ThreeSum.LightWeightedBankAssembly.program_length : program.length=17 := by sorry

attribute [defeq] ThreeSum.LightWeightedBankAssembly.program_length

-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryBankAssembly_program_length
-- name    : ThreeSum.LightTernaryBankAssembly.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:00:18.57064+00:00
-- url     : https://prove2.me/theorems/6db94077-bcb3-4782-9da5-5dd1b82109d2
-- title:
--   Light Ternary Bank Assembly: program length
-- statement:
--   The Light Ternary Bank Assembly construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankAssembly.lean#L37-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryBankAssembly.lean#L37-L37

import Definitions.Def_Submission_ThreeSum_LightTernaryBankStages
import Definitions.Def_Submission_ThreeSum_LightTernaryProduct
import Definitions.Def_Submission_ThreeSum_LightTernaryBankAssembly
import Theorems.Thm_ThreeSum_LightTernaryBankStages_program_length
attribute [local simp] ThreeSum.LightTernaryBankStages.program_length


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankAssembly
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightTernaryBankSweep
set_option maxHeartbeats 6000000
variable {lim : Limits}

theorem ThreeSum.LightTernaryBankAssembly.program_length : program.length=17 := by sorry

attribute [defeq] ThreeSum.LightTernaryBankAssembly.program_length

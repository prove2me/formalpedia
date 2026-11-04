-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPreparedWanted_program_length
-- name    : ThreeSum.LightTernaryPreparedWanted.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:42:22.199553+00:00
-- url     : https://prove2.me/theorems/88bff5f4-ba0a-4301-ba44-ca951c1c572f
-- title:
--   Light Ternary Prepared Wanted: program length
-- statement:
--   The Light Ternary Prepared Wanted construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPreparedWanted.lean#L152-L152
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPreparedWanted.lean#L152-L152

import Definitions.Def_Submission_ThreeSum_LightTernaryQueryPlan
import Definitions.Def_Submission_ThreeSum_TernaryNearCanonical
import Definitions.Def_Submission_ThreeSum_LightTernaryPreparedWanted
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightTernaryBankStages_program_length
import Theorems.Thm_ThreeSum_LightTernaryNearPair_program_length
import Theorems.Thm_ThreeSum_LightTernaryNearSetup_program_length
import Theorems.Thm_ThreeSum_LightTernaryWantedQuery_program_length
attribute [local simp] ThreeSum.LightTernaryBankAssembly.program_length
attribute [local simp] ThreeSum.LightTernaryBankStages.program_length
attribute [local simp] ThreeSum.LightTernaryNearPair.program_length
attribute [local simp] ThreeSum.LightTernaryNearSetup.program_length
attribute [local simp] ThreeSum.LightTernaryWantedQuery.program_length


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPreparedWanted
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryBankStageModel ThreeSum.LightTernaryNearPair ThreeSum.LightTernaryQueryPlan
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryPreparedWanted.program_length : program.length=28 := by sorry

attribute [defeq] ThreeSum.LightTernaryPreparedWanted.program_length

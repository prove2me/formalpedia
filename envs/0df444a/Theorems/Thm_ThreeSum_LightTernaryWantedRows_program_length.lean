-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryWantedRows_program_length
-- name    : ThreeSum.LightTernaryWantedRows.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:04:55.214199+00:00
-- url     : https://prove2.me/theorems/4d054361-c95c-4955-ae45-f3e2b05a4460
-- title:
--   Light Ternary Wanted Rows: program length
-- statement:
--   The Light Ternary Wanted Rows construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedRows.lean#L158-L158
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedRows.lean#L158-L158

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedRowDispatch
import Definitions.Def_Submission_ThreeSum_LightTernaryPreparedState
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedRows
import Theorems.Thm_ThreeSum_LightTernaryBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightTernaryBankStages_program_length
import Theorems.Thm_ThreeSum_LightTernaryNearPair_program_length
import Theorems.Thm_ThreeSum_LightTernaryNearSetup_program_length
import Theorems.Thm_ThreeSum_LightTernaryPreparedWanted_program_length
import Theorems.Thm_ThreeSum_LightTernaryWantedQuery_program_length
attribute [local simp] ThreeSum.LightTernaryBankAssembly.program_length
attribute [local simp] ThreeSum.LightTernaryBankStages.program_length
attribute [local simp] ThreeSum.LightTernaryNearPair.program_length
attribute [local simp] ThreeSum.LightTernaryNearSetup.program_length
attribute [local simp] ThreeSum.LightTernaryPreparedWanted.program_length
attribute [local simp] ThreeSum.LightTernaryWantedQuery.program_length


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryWantedRows
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryBankStageModel
open ThreeSum.LightTernaryNearPair ThreeSum.LightTernaryWantedRowDispatch ThreeSum.LightTernaryPreparedState
set_option maxHeartbeats 7000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryWantedRows.program_length : program.length=30 := by sorry

attribute [defeq] ThreeSum.LightTernaryWantedRows.program_length

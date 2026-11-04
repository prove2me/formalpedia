-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedWantedRows_program_length
-- name    : ThreeSum.LightWeightedWantedRows.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:06:20.792928+00:00
-- url     : https://prove2.me/theorems/eaa4a1a7-fb25-4f7e-9248-db9639628fc3
-- title:
--   Light Weighted Wanted Rows: program length
-- statement:
--   The Light Weighted Wanted Rows construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/WantedRows.lean#L164-L164
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/WantedRows.lean#L164-L164

import Definitions.Def_Submission_Weighted_WantedRowDispatch
import Definitions.Def_Submission_Weighted_PreparedState
import Definitions.Def_Submission_Weighted_WantedRows
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightWeightedBankStages_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearPair_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearSetup_program_length
import Theorems.Thm_ThreeSum_LightWeightedPreparedWanted_program_length
import Theorems.Thm_ThreeSum_LightWeightedWantedQuery_program_length
attribute [local simp] ThreeSum.LightWeightedBankAssembly.program_length
attribute [local simp] ThreeSum.LightWeightedBankStages.program_length
attribute [local simp] ThreeSum.LightWeightedNearPair.program_length
attribute [local simp] ThreeSum.LightWeightedNearSetup.program_length
attribute [local simp] ThreeSum.LightWeightedPreparedWanted.program_length
attribute [local simp] ThreeSum.LightWeightedWantedQuery.program_length


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedWantedRows
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.WeightedBankStageModel
open ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedWantedRowDispatch ThreeSum.LightWeightedPreparedState
set_option maxHeartbeats 7000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedWantedRows.program_length : program.length=43 := by sorry

attribute [defeq] ThreeSum.LightWeightedWantedRows.program_length

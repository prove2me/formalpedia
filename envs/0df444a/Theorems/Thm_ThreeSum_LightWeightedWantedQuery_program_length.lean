-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedWantedQuery_program_length
-- name    : ThreeSum.LightWeightedWantedQuery.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:20:02.833982+00:00
-- url     : https://prove2.me/theorems/59b7fe8a-d722-4315-a5d6-45a45668e525
-- title:
--   Light Weighted Wanted Query: program length
-- statement:
--   The Light Weighted Wanted Query construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/WantedQuery.lean#L151-L151
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/WantedQuery.lean#L151-L151

import Definitions.Def_Submission_Weighted_NearPair
import Definitions.Def_Submission_Weighted_FrozenPhysical
import Definitions.Def_Submission_Weighted_BankAssembly
import Definitions.Def_Submission_Weighted_WantedQuery
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightWeightedBankStages_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearPair_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearSetup_program_length
attribute [local simp] ThreeSum.LightWeightedBankAssembly.program_length
attribute [local simp] ThreeSum.LightWeightedBankStages.program_length
attribute [local simp] ThreeSum.LightWeightedNearPair.program_length
attribute [local simp] ThreeSum.LightWeightedNearSetup.program_length


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedWantedQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.WeightedBankStageModel
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.LightWeightedNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedWantedQuery.program_length : program.length=40 := by sorry

attribute [defeq] ThreeSum.LightWeightedWantedQuery.program_length

-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedPreparedWanted_program_length
-- name    : ThreeSum.LightWeightedPreparedWanted.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:42:35.178869+00:00
-- url     : https://prove2.me/theorems/6c91aba9-fd72-47fd-a672-62254b764590
-- title:
--   Light Weighted Prepared Wanted: program length
-- statement:
--   The Light Weighted Prepared Wanted construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PreparedWanted.lean#L153-L153
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PreparedWanted.lean#L153-L153

import Definitions.Def_Submission_Weighted_QueryPlan
import Definitions.Def_Submission_Weighted_NearCanonical
import Definitions.Def_Submission_Weighted_PreparedWanted
import Theorems.Thm_ThreeSum_LightWeightedBankAssembly_program_length
import Theorems.Thm_ThreeSum_LightWeightedBankStages_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearPair_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearSetup_program_length
import Theorems.Thm_ThreeSum_LightWeightedWantedQuery_program_length
attribute [local simp] ThreeSum.LightWeightedBankAssembly.program_length
attribute [local simp] ThreeSum.LightWeightedBankStages.program_length
attribute [local simp] ThreeSum.LightWeightedNearPair.program_length
attribute [local simp] ThreeSum.LightWeightedNearSetup.program_length
attribute [local simp] ThreeSum.LightWeightedWantedQuery.program_length


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedPreparedWanted
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
open ThreeSum.WeightedBankStageModel ThreeSum.LightWeightedNearPair ThreeSum.LightWeightedQueryPlan
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedPreparedWanted.program_length : program.length=41 := by sorry

attribute [defeq] ThreeSum.LightWeightedPreparedWanted.program_length

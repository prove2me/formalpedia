-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedNearPair_program_length
-- name    : ThreeSum.LightWeightedNearPair.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:06:39.337079+00:00
-- url     : https://prove2.me/theorems/7aa31ea4-0a0c-49ef-ba08-cb2aeddad100
-- title:
--   Light Weighted Near Pair: program length
-- statement:
--   The Light Weighted Near Pair construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearPair.lean#L237-L237
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearPair.lean#L237-L237

import Definitions.Def_Submission_Weighted_KernelProgram
import Definitions.Def_Submission_Weighted_NearSourceWords
import Definitions.Def_Submission_Weighted_NearPair
import Theorems.Thm_ThreeSum_LightWeightedBankStages_program_length
import Theorems.Thm_ThreeSum_LightWeightedNearSetup_program_length
attribute [local simp] ThreeSum.LightWeightedBankStages.program_length
attribute [local simp] ThreeSum.LightWeightedNearSetup.program_length


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedNearPair
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedNearPair.program_length : program.length=39 := by sorry

attribute [defeq] ThreeSum.LightWeightedNearPair.program_length

-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedNearSetup_program_length
-- name    : ThreeSum.LightWeightedNearSetup.program_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:06:05.443837+00:00
-- url     : https://prove2.me/theorems/5f642ae2-ad6c-4e26-9621-317914d40cf6
-- title:
--   Light Weighted Near Setup: program length
-- statement:
--   The Light Weighted Near Setup construction uses the program length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearSetup.lean#L115-L115
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearSetup.lean#L115-L115

import Definitions.Def_Submission_Weighted_NearDigits
import Definitions.Def_Submission_Weighted_LightNearEnumerationMain
import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearSetup
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedNearSetup
open Light ThreeSum.LightSubsetAddress
open ThreeSum.WeightedEnumeration (digitCost)
open ThreeSum.TernaryJointType ThreeSum.WeightedBankEnumeration ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedNearSetup.program_length : program.length=7 := by sorry

attribute [defeq] ThreeSum.LightWeightedNearSetup.program_length

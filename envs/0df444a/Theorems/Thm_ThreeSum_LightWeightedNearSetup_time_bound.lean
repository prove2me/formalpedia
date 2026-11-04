-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedNearSetup_time_bound
-- name    : ThreeSum.LightWeightedNearSetup.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:06:10.42691+00:00
-- url     : https://prove2.me/theorems/1ba1d595-4359-409d-9006-d96e2dec3e08
-- title:
--   Light Weighted Near Setup: time bound
-- statement:
--   The Light Weighted Near Setup construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearSetup.lean#L103-L108
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/NearSetup.lean#L103-L108

import Definitions.Def_Submission_Weighted_NearDigits
import Definitions.Def_Submission_Weighted_LightNearEnumerationMain
import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearSetup
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedNearSetup
open Light ThreeSum.LightSubsetAddress
open ThreeSum.WeightedEnumeration (digitCost)
open ThreeSum.TernaryJointType ThreeSum.WeightedBankEnumeration ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedNearSetup.time_bound {N : ℕ} (Q : TritWord N) (D : ℕ) :
    time Q D≤3000*(N+1)^2*((WeightedNearEnumeration.codes (wordList Q) D).length+1) := by sorry

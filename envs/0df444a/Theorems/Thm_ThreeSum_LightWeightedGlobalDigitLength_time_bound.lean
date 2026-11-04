-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalDigitLength_time_bound
-- name    : ThreeSum.LightWeightedGlobalDigitLength.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:27:16.121978+00:00
-- url     : https://prove2.me/theorems/eae42c03-fe91-4560-b43d-6b7ffa9e0add
-- title:
--   Light Weighted Global Digit Length: time bound
-- statement:
--   The Light Weighted Global Digit Length construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryDigitLength.lean#L112-L121
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryDigitLength.lean#L112-L121

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernarySignedPadding
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_Weighted_Global_LightTernaryDigitLength
import Theorems.Thm_ThreeSum_LightCacheEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightTernaryDivide_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_time_bound
import Theorems.Thm_ThreeSum_LightTernaryInversePass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryQueryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryRankTable_time_bound
import Theorems.Thm_ThreeSum_LightWeightedEulerMetadata_time_bound
import Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightWeightedNearSetup_time_bound
import Theorems.Thm_ThreeSum_LightWeightedNearSource_time_bound
import Theorems.Thm_ThreeSum_LightWeightedPredecessorTable_time_bound
import Theorems.Thm_ThreeSum_LightWeightedPredecessor_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalDigitLength
open Light WeightedGlobalSignedPadding
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightWeightedGlobalDigitLength.time_bound {b : ℕ} (hb : 1<b) (U : ℕ) :
    time b U≤20*Nat.log 2 (3*U+1)+120 := by sorry

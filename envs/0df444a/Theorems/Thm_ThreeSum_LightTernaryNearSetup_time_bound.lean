-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryNearSetup_time_bound
-- name    : ThreeSum.LightTernaryNearSetup.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:21:15.372543+00:00
-- url     : https://prove2.me/theorems/f0754bc7-0993-46dd-b1f1-9a0ef5ee3ab5
-- title:
--   Light Ternary Near Setup: time bound
-- statement:
--   The Light Ternary Near Setup construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearSetup.lean#L96-L101
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearSetup.lean#L96-L101

import Definitions.Def_Submission_ThreeSum_LightTernaryNearDigits
import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumerationMain
import Definitions.Def_Submission_ThreeSum_TernaryNearCanonical
import Definitions.Def_Submission_ThreeSum_LightTernaryNearSetup
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightTernaryDivide_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerMemo_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerMetadata_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_time_bound
import Theorems.Thm_ThreeSum_LightTernaryLookup_time_bound
import Theorems.Thm_ThreeSum_LightTernaryNearEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightTernaryNearSource_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPass_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPredecessorTable_time_bound
import Theorems.Thm_ThreeSum_LightTernaryPredecessor_time_bound
import Theorems.Thm_ThreeSum_LightTernaryRankTable_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryNearSetup
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBankEnumeration ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryNearSetup.time_bound {N : ℕ} (Q : TritWord N) (D : ℕ) :
    time Q D≤3000*(N+1)^2*((TernaryNearEnumeration.codes (wordList Q) D).length+1) := by sorry

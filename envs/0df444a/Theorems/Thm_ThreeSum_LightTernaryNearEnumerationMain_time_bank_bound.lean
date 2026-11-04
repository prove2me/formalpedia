-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryNearEnumerationMain_time_bank_bound
-- name    : ThreeSum.LightTernaryNearEnumerationMain.time_bank_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:59:20.748214+00:00
-- url     : https://prove2.me/theorems/2096b91b-d901-4e54-845d-2e7e9760d40c
-- title:
--   Light Ternary Near Enumeration Main: time bank bound
-- statement:
--   The Light Ternary Near Enumeration Main construction uses the time bank bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearEnumerationMain.lean#L236-L239
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearEnumerationMain.lean#L236-L239

import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumerationMain
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryNearEnumerationMain
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryAddresses
open ThreeSum.TernaryNearEnumeration ThreeSum.LightTernaryNearEnumeration
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryNearEnumerationMain.time_bank_bound {N : ℕ} (Q : ThreeSum.TernaryJointType.TritWord N) (D : ℕ) :
    time (ThreeSum.TernaryBankEnumeration.wordList Q) D ≤
      900*((N+1)*(ThreeSum.TernaryBank.nearWords Q D).card) := by sorry

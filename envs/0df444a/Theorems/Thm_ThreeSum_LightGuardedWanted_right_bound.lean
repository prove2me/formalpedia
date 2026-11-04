-- Prove2me | Theorems.Thm_ThreeSum_LightGuardedWanted_right_bound
-- name    : ThreeSum.LightGuardedWanted.right_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:17:29.892609+00:00
-- url     : https://prove2.me/theorems/cfab79e6-83e9-4446-ac35-e21d2c616d8b
-- title:
--   Light Guarded Wanted: right bound
-- statement:
--   The Light Guarded Wanted construction uses the right bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightGuardedWanted.lean#L78-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightGuardedWanted.lean#L78-L87

import Definitions.Def_Submission_ThreeSum_LightCoverKeyData
import Definitions.Def_Submission_ThreeSum_LightRawAKeys
import Definitions.Def_Submission_ThreeSum_LightBalancedWanted
import Definitions.Def_Submission_ThreeSum_LightGuardedWanted
set_option autoImplicit false
open ThreeSum ThreeSum.LightGuardedWanted
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000

theorem ThreeSum.LightGuardedWanted.right_bound (h J P : ℕ) (j : ℕ) (hj : j < totalKeys h J) :
    |right h J j| ≤ (keyBound P h J : ℤ) := by sorry

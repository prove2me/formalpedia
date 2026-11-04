-- Prove2me | Theorems.Thm_ThreeSum_LightGuardedWanted_left_bound
-- name    : ThreeSum.LightGuardedWanted.left_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:17:07.762533+00:00
-- url     : https://prove2.me/theorems/7e1b2a42-ba4b-43a6-8289-4fbedc0fd919
-- title:
--   Light Guarded Wanted: left bound
-- statement:
--   The Light Guarded Wanted construction uses the left bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightGuardedWanted.lean#L68-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightGuardedWanted.lean#L68-L76

import Definitions.Def_Submission_ThreeSum_LightCoverKeyData
import Definitions.Def_Submission_ThreeSum_LightRawAKeys
import Definitions.Def_Submission_ThreeSum_LightBalancedWanted
import Definitions.Def_Submission_ThreeSum_LightGuardedWanted
set_option autoImplicit false
open ThreeSum ThreeSum.LightGuardedWanted
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000

theorem ThreeSum.LightGuardedWanted.left_bound {P h J : ℕ} (hP : 0 < P) (xs : List ℤ) (i : ℕ) (hi : i < 3*xs.length) :
    |left P xs i| ≤ (keyBound P h J : ℤ) := by sorry

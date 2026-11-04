-- Prove2me | Theorems.Thm_ThreeSum_LightPairFlags_time_bound
-- name    : ThreeSum.LightPairFlags.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:31:55.894888+00:00
-- url     : https://prove2.me/theorems/de9cb0f5-389e-4caa-ad1a-dcf317e31885
-- title:
--   Light Pair Flags: time bound
-- statement:
--   The Light Pair Flags construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPairFlags.lean#L270-L276
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPairFlags.lean#L270-L276

import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightTrimTest
import Definitions.Def_Submission_ThreeSum_LightPairFlags
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightPairFlags
open Light
set_option maxHeartbeats 1500000
set_option maxRecDepth 5000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightPairFlags.time_bound (L n : ℕ) : time L n ≤ 500*(n*n)*(L+n+1)+30 := by sorry

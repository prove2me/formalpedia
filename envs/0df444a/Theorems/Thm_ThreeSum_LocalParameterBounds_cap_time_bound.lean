-- Prove2me | Theorems.Thm_ThreeSum_LocalParameterBounds_cap_time_bound
-- name    : ThreeSum.LocalParameterBounds.cap_time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:36:26.579193+00:00
-- url     : https://prove2.me/theorems/83fc5b72-1715-4c75-a387-d1bb5f356dc9
-- title:
--   Local Parameter Bounds: cap time bound
-- statement:
--   The Local Parameter Bounds construction uses the cap time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalParameterBounds.lean#L73-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalParameterBounds.lean#L73-L87

import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
set_option autoImplicit false
open ThreeSum ThreeSum.LocalParameterBounds
open LocalCoverBounds
set_option maxHeartbeats 1000000

theorem ThreeSum.LocalParameterBounds.cap_time_bound (h : ℕ) :
    LightSmallDivide.time (LightLocalParameters.numerator h) (localPrime h) ≤ 2^(514*h+10) := by sorry

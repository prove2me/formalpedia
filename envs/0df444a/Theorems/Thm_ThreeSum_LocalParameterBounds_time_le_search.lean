-- Prove2me | Theorems.Thm_ThreeSum_LocalParameterBounds_time_le_search
-- name    : ThreeSum.LocalParameterBounds.time_le_search
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:47:31.808502+00:00
-- url     : https://prove2.me/theorems/65108776-5d9c-4eae-ba23-448fb40b1d41
-- title:
--   Local Parameter Bounds: time le search
-- statement:
--   The Local Parameter Bounds construction uses the time le search property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalParameterBounds.lean#L186-L188
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalParameterBounds.lean#L186-L188

import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
set_option autoImplicit false
open ThreeSum ThreeSum.LocalParameterBounds
open LocalCoverBounds
set_option maxHeartbeats 1000000

theorem ThreeSum.LocalParameterBounds.time_le_search {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    LightLocalParameters.time (Scales.microHalf (Scales.inputBits n)) ≤ Scales.localSearch 2000 n := by sorry

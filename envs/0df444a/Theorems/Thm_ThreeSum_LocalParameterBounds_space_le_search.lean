-- Prove2me | Theorems.Thm_ThreeSum_LocalParameterBounds_space_le_search
-- name    : ThreeSum.LocalParameterBounds.space_le_search
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:47:26.235513+00:00
-- url     : https://prove2.me/theorems/21af3b69-c0f0-4db8-8881-177743680b54
-- title:
--   Local Parameter Bounds: space le search
-- statement:
--   The Local Parameter Bounds construction uses the space le search property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalParameterBounds.lean#L194-L197
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalParameterBounds.lean#L194-L197

import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
set_option autoImplicit false
open ThreeSum ThreeSum.LocalParameterBounds
open LocalCoverBounds
set_option maxHeartbeats 1000000

theorem ThreeSum.LocalParameterBounds.space_le_search {n work : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    LightLocalParameters.space work (Scales.microHalf (Scales.inputBits n)) ≤
      work+Scales.localSearch 2000 n := by sorry

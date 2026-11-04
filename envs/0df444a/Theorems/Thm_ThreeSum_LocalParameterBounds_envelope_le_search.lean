-- Prove2me | Theorems.Thm_ThreeSum_LocalParameterBounds_envelope_le_search
-- name    : ThreeSum.LocalParameterBounds.envelope_le_search
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:46:21.162254+00:00
-- url     : https://prove2.me/theorems/ad6e9677-2aa2-4cc0-b84e-3b8b4b604550
-- title:
--   Local Parameter Bounds: envelope le search
-- statement:
--   The Local Parameter Bounds construction uses the envelope le search property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalParameterBounds.lean#L179-L184
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LocalParameterBounds.lean#L179-L184

import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
set_option autoImplicit false
open ThreeSum ThreeSum.LocalParameterBounds
open LocalCoverBounds
set_option maxHeartbeats 1000000

theorem ThreeSum.LocalParameterBounds.envelope_le_search {n : ℕ} (hh : 1 ≤ Scales.microHalf (Scales.inputBits n)) :
    envelope (Scales.microHalf (Scales.inputBits n)) ≤ Scales.localSearch 2000 n := by sorry

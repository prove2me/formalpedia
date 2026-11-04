-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryCodes_digit_time_bound
-- name    : ThreeSum.LightTernaryCodes.digit_time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:56:03.119975+00:00
-- url     : https://prove2.me/theorems/d84a3ade-bec3-46ae-bcf0-6c226b8cec59
-- title:
--   Light Ternary Codes: digit time bound
-- statement:
--   The Light Ternary Codes construction uses the digit time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCodes.lean#L127-L129
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCodes.lean#L127-L129

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCodes
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryCodes.digit_time_bound (W : ℕ) : digitTime W ≤ 400*(W+1) := by sorry

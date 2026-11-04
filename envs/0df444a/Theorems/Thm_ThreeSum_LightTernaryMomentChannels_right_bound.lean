-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryMomentChannels_right_bound
-- name    : ThreeSum.LightTernaryMomentChannels.right_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:46:56.238226+00:00
-- url     : https://prove2.me/theorems/03bc430e-9b85-40d7-9412-6383d87fdf43
-- title:
--   Light Ternary Moment Channels: right bound
-- statement:
--   The Light Ternary Moment Channels construction uses the right bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentChannels.lean#L18-L20
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentChannels.lean#L18-L20

import Definitions.Def_Submission_ThreeSum_LightTernaryScalarChannel
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannels
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMomentChannels
open Light LightFixedArithmetic TernaryWeightChannels

theorem ThreeSum.LightTernaryMomentChannels.right_bound (k j : ℕ) (U : ℤ) :
    (rightMoment k j).bound U=2*(U+1)^(k-j) := by sorry

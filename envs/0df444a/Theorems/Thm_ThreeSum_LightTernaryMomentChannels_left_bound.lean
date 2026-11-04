-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryMomentChannels_left_bound
-- name    : ThreeSum.LightTernaryMomentChannels.left_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:46:40.901858+00:00
-- url     : https://prove2.me/theorems/4dc1b1d9-715c-4777-bca6-b4075b16bdcf
-- title:
--   Light Ternary Moment Channels: left bound
-- statement:
--   The Light Ternary Moment Channels construction uses the left bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentChannels.lean#L13-L16
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryMomentChannels.lean#L13-L16

import Definitions.Def_Submission_ThreeSum_LightTernaryScalarChannel
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannels
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMomentChannels
open Light LightFixedArithmetic TernaryWeightChannels

theorem ThreeSum.LightTernaryMomentChannels.left_bound (k j : ℕ) (U : ℤ) :
    (leftMoment k j).bound U=2*((k.choose j : ℤ)+1)*(U+2)^j := by sorry

-- Prove2me | Theorems.Thm_ThreeSum_TernaryWeightChannels_leftMoment_eval
-- name    : ThreeSum.TernaryWeightChannels.leftMoment_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:40:33.274998+00:00
-- url     : https://prove2.me/theorems/197f2871-8c27-4f93-8784-03405f9dd43d
-- title:
--   Ternary Weight Channels: left Moment eval
-- statement:
--   The Ternary Weight Channels construction uses the left Moment eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWeightChannels.lean#L26-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWeightChannels.lean#L26-L28

import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWeightChannels
open Finset LightFixedArithmetic TernaryJointType TernaryWeightedPhysicalSources
open scoped BigOperators

theorem ThreeSum.TernaryWeightChannels.leftMoment_eval (k j : ℕ) (x : ℕ→ℤ) :
    (leftMoment k j).eval x=(k.choose j : ℤ)*(-(x 0))^j := by sorry

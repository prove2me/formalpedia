-- Prove2me | Theorems.Thm_ThreeSum_TernaryWeightChannels_rightMoment_eval
-- name    : ThreeSum.TernaryWeightChannels.rightMoment_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:40:35.948217+00:00
-- url     : https://prove2.me/theorems/f3a6a2e7-4a7f-4e1d-9f24-39c46d0803c3
-- title:
--   Ternary Weight Channels: right Moment eval
-- statement:
--   The Ternary Weight Channels construction uses the right Moment eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWeightChannels.lean#L29-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWeightChannels.lean#L29-L30

import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWeightChannels
open Finset LightFixedArithmetic TernaryJointType TernaryWeightedPhysicalSources
open scoped BigOperators

theorem ThreeSum.TernaryWeightChannels.rightMoment_eval (k j : ℕ) (x : ℕ→ℤ) :
    (rightMoment k j).eval x=(x 0)^(k-j) := by sorry

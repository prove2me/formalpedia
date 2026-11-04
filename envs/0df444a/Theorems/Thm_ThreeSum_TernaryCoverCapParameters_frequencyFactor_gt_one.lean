-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverCapParameters_frequencyFactor_gt_one
-- name    : ThreeSum.TernaryCoverCapParameters.frequencyFactor_gt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:32:22.32629+00:00
-- url     : https://prove2.me/theorems/8641dab1-22a8-4d79-9d36-21805bb31914
-- title:
--   Ternary Cover Cap Parameters: frequency Factor gt one
-- statement:
--   The Ternary Cover Cap Parameters construction uses the frequency Factor gt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverCapParameters.lean#L80-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverCapParameters.lean#L80-L87

import Definitions.Def_Submission_ThreeSum_TernaryCoverFrequency
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverCapParameters
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryCoverGoodMaps TernaryCoverFrequency TernaryPartitionCount TernaryTypeLowerBound

theorem ThreeSum.TernaryCoverCapParameters.frequencyFactor_gt_one (m : ℕ) : 1 < frequencyFactor m := by sorry

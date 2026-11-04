-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalLocalParameters_difference_choose_le_partition
-- name    : ThreeSum.WeightedGlobalLocalParameters.difference_choose_le_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:57:51.750299+00:00
-- url     : https://prove2.me/theorems/f00d21e0-9b4f-4636-a2e0-0761ec8702f5
-- title:
--   Weighted Global Local Parameters: difference choose le partition
-- statement:
--   The exceptional difference-fiber cap is smaller than the partition cap
--   in every exact integer instance of the certified rational schedule.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalLocalParameters.lean#L60-L72
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalLocalParameters.lean#L60-L72

import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformProjection
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalLocalParameters
open Finset TernaryJointType TernaryCoverLocal TernaryTypeLowerBound TernaryCoverUniformProjection

theorem ThreeSum.WeightedGlobalLocalParameters.difference_choose_le_partition (m : ℕ) :
    (fixedLength m).choose (fixedPi m 2/3) ≤ 2^(fixedPi m 1)*3^(fixedPi m 2) := by sorry

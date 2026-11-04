-- Prove2me | Theorems.Thm_ThreeSum_TernaryLocalParameters_difference_choose_le_partition
-- name    : ThreeSum.TernaryLocalParameters.difference_choose_le_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:47:37.283124+00:00
-- url     : https://prove2.me/theorems/ed181a91-e1f4-4d40-8740-4a9693a23451
-- title:
--   Ternary Local Parameters: difference choose le partition
-- statement:
--   The exceptional difference-fiber cap is smaller than the partition cap
--   in every exact integer instance of the certified rational schedule.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryLocalParameters.lean#L54-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryLocalParameters.lean#L54-L66

import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformProjection
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryLocalParameters
open Finset TernaryJointType TernaryCoverLocal TernaryTypeLowerBound TernaryCoverUniformProjection

theorem ThreeSum.TernaryLocalParameters.difference_choose_le_partition (m : ℕ) :
    (fixedLength m).choose (fixedPi m 2/3) ≤ 2^(fixedPi m 1)*3^(fixedPi m 2) := by sorry

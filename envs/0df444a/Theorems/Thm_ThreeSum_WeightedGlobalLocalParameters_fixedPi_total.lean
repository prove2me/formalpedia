-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalLocalParameters_fixedPi_total
-- name    : ThreeSum.WeightedGlobalLocalParameters.fixedPi_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:12:27.773639+00:00
-- url     : https://prove2.me/theorems/4983e12f-3569-47c5-b200-a54aa5f1c727
-- title:
--   Weighted Global Local Parameters: fixed Pi total
-- statement:
--   The Weighted Global Local Parameters construction uses the fixed Pi total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalLocalParameters.lean#L19-L21
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalLocalParameters.lean#L19-L21

import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformProjection
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalLocalParameters
open Finset TernaryJointType TernaryCoverLocal TernaryTypeLowerBound TernaryCoverUniformProjection

theorem ThreeSum.WeightedGlobalLocalParameters.fixedPi_total (m : ℕ) : fixedPi m 0+fixedPi m 1+fixedPi m 2 = fixedLength m := by sorry

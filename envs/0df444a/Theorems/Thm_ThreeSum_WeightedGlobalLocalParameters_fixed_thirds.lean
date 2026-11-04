-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalLocalParameters_fixed_thirds
-- name    : ThreeSum.WeightedGlobalLocalParameters.fixed_thirds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:57:38.340317+00:00
-- url     : https://prove2.me/theorems/150d8568-6110-41ca-ba95-2c0e244966a6
-- title:
--   Weighted Global Local Parameters: fixed thirds
-- statement:
--   The Weighted Global Local Parameters construction uses the fixed thirds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalLocalParameters.lean#L27-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalLocalParameters.lean#L27-L29

import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformProjection
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalLocalParameters
open Finset TernaryJointType TernaryCoverLocal TernaryTypeLowerBound TernaryCoverUniformProjection

theorem ThreeSum.WeightedGlobalLocalParameters.fixed_thirds (m : ℕ) : fixedPi m 2 = 3*(fixedAlpha m 2) := by sorry

-- Prove2me | Theorems.Thm_ThreeSum_TernaryLocalParameters_fixedPi_total
-- name    : ThreeSum.TernaryLocalParameters.fixedPi_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:12:30.588345+00:00
-- url     : https://prove2.me/theorems/f3e9f963-d6f3-4393-a8cd-585dd37eebe4
-- title:
--   Ternary Local Parameters: fixed Pi total
-- statement:
--   The Ternary Local Parameters construction uses the fixed Pi total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryLocalParameters.lean#L13-L15
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryLocalParameters.lean#L13-L15

import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformProjection
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryLocalParameters
open Finset TernaryJointType TernaryCoverLocal TernaryTypeLowerBound TernaryCoverUniformProjection

theorem ThreeSum.TernaryLocalParameters.fixedPi_total (m : ℕ) : fixedPi m 0+fixedPi m 1+fixedPi m 2 = fixedLength m := by sorry

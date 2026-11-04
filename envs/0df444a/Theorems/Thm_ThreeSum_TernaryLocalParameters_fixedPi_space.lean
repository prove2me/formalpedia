-- Prove2me | Theorems.Thm_ThreeSum_TernaryLocalParameters_fixedPi_space
-- name    : ThreeSum.TernaryLocalParameters.fixedPi_space
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:12:46.020985+00:00
-- url     : https://prove2.me/theorems/8da98fe5-e212-485a-b9c7-8e854329545f
-- title:
--   Ternary Local Parameters: fixed Pi space
-- statement:
--   The Ternary Local Parameters construction uses the fixed Pi space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryLocalParameters.lean#L17-L19
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryLocalParameters.lean#L17-L19

import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformProjection
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryLocalParameters
open Finset TernaryJointType TernaryCoverLocal TernaryTypeLowerBound TernaryCoverUniformProjection

theorem ThreeSum.TernaryLocalParameters.fixedPi_space (m : ℕ) : 2*(fixedPi m 1)+3*(fixedPi m 2) ≤ fixedLength m := by sorry

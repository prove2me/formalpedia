-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalLocalParameters_fixedPi_space
-- name    : ThreeSum.WeightedGlobalLocalParameters.fixedPi_space
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:12:28.354219+00:00
-- url     : https://prove2.me/theorems/80efb669-6b91-4cff-8d80-33a051581113
-- title:
--   Weighted Global Local Parameters: fixed Pi space
-- statement:
--   The Weighted Global Local Parameters construction uses the fixed Pi space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalLocalParameters.lean#L23-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalLocalParameters.lean#L23-L25

import Definitions.Def_Submission_ThreeSum_TernaryCoverUniformProjection
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalLocalParameters
open Finset TernaryJointType TernaryCoverLocal TernaryTypeLowerBound TernaryCoverUniformProjection

theorem ThreeSum.WeightedGlobalLocalParameters.fixedPi_space (m : ℕ) : 2*(fixedPi m 1)+3*(fixedPi m 2) ≤ fixedLength m := by sorry

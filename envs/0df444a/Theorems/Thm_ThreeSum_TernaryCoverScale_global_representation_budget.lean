-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverScale_global_representation_budget
-- name    : ThreeSum.TernaryCoverScale.global_representation_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:51:21.399198+00:00
-- url     : https://prove2.me/theorems/bcf31f46-ab83-45d3-80e5-cffac8e73dc6
-- title:
--   Ternary Cover Scale: global representation budget
-- statement:
--   This bridge charges every polynomial carry choice and every repeated
--   family/raw-cap choice. Its only global assumption is the displayed radix
--   bound; it supplies no implementation time bound.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverScale.lean#L228-L245
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverScale.lean#L228-L245

import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverScale
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryTypeLowerBound TernaryCoverCapParameters TernaryCoverFrequency

theorem ThreeSum.TernaryCoverScale.global_representation_budget (c d a n r : ℕ)
    (hradix : prime (scale 40000000000 c d)^r ≤ a*n^3) (han : a ≤ n) :
    ((localFactor 40000000000 c d)^r : ℝ) ≤ (n : ℝ)^(1/10000000000 : ℝ) := by sorry

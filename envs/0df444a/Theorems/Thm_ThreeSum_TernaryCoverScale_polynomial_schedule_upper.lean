-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverScale_polynomial_schedule_upper
-- name    : ThreeSum.TernaryCoverScale.polynomial_schedule_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:50:34.411532+00:00
-- url     : https://prove2.me/theorems/e4d7b940-9f40-429d-8e34-2d97e6cca584
-- title:
--   Ternary Cover Scale: polynomial schedule upper
-- statement:
--   The Ternary Cover Scale construction uses the polynomial schedule upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverScale.lean#L155-L167
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverScale.lean#L155-L167

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

theorem ThreeSum.TernaryCoverScale.polynomial_schedule_upper (c d t : ℕ) (hc : c ≤ t) :
    (c*(fixedLength (2^(2*t))+1)^d)*
      (frequencyFactor (2^(2*t))*(Nat.log2 (prime (2^(2*t))^2)+1)) ≤
    2^(28*d+241+(2*d+15)*t) := by sorry

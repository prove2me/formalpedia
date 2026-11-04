-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_polynomial_schedule_upper
-- name    : ThreeSum.WeightedGlobalCoverScale.polynomial_schedule_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:59:08.909531+00:00
-- url     : https://prove2.me/theorems/caf75f9b-0b17-4cb9-a838-1d484aa28561
-- title:
--   Weighted Global Cover Scale: polynomial schedule upper
-- statement:
--   The Weighted Global Cover Scale construction uses the polynomial schedule upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L162-L174
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L162-L174

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverScale
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open TernaryTypeLowerBound WeightedGlobalCoverCapParameters WeightedGlobalCoverFrequency

theorem ThreeSum.WeightedGlobalCoverScale.polynomial_schedule_upper (c d t : ℕ) (hc : c ≤ t) :
    (c*(fixedLength (2^(2*t))+1)^d)*
      (frequencyFactor (2^(2*t))*(Nat.log2 (prime (2^(2*t))^2)+1)) ≤
    2^(46*d+367+(2*d+15)*t) := by sorry

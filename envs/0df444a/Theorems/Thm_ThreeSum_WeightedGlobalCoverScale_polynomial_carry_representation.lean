-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_polynomial_carry_representation
-- name    : ThreeSum.WeightedGlobalCoverScale.polynomial_carry_representation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:58:11.705198+00:00
-- url     : https://prove2.me/theorems/e4427737-bf97-40a3-9786-d4bdd7870a3c
-- title:
--   Weighted Global Cover Scale: polynomial carry representation
-- statement:
--   The bound applies to any actual carry count below the polynomial
--   envelope, rather than requiring that count to equal its envelope.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L327-L340
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L327-L340

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

theorem ThreeSum.WeightedGlobalCoverScale.polynomial_carry_representation (c d b : ℕ)
    (hb : b ≤ c*(fixedLength (scale 40000000000 c d)+1)^d) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((b*(family (scale 40000000000 c d) (momentOrder 40000000000)).length*
        rawThreshold (prime (scale 40000000000 c d))
          (sourceCap (scale 40000000000 c d) (prime (scale 40000000000 c d)))
          (momentOrder 40000000000))^
          (radixLength (scale 40000000000 c d) n) : ℝ) ≤
        (n : ℝ)^(1/10000000000 : ℝ) := by sorry

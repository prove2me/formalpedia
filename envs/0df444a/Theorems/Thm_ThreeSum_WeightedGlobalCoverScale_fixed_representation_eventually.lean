-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_fixed_representation_eventually
-- name    : ThreeSum.WeightedGlobalCoverScale.fixed_representation_eventually
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:01:11.531415+00:00
-- url     : https://prove2.me/theorems/05e9fec2-0573-47d9-a655-5a266e88c289
-- title:
--   Weighted Global Cover Scale: fixed representation eventually
-- statement:
--   A completely specified fixed block and radix schedule pay all repeated
--   cover and polynomial carry multiplicities within the 10^-10 allowance.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L309-L316
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L309-L316

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

theorem ThreeSum.WeightedGlobalCoverScale.fixed_representation_eventually (c d : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((localFactor 40000000000 c d)^
        (radixLength (scale 40000000000 c d) n) : ℝ) ≤
          (n : ℝ)^(1/10000000000 : ℝ) := by sorry

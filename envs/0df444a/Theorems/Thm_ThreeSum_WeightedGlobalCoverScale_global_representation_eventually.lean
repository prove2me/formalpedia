-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_global_representation_eventually
-- name    : ThreeSum.WeightedGlobalCoverScale.global_representation_eventually
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:03:28.21469+00:00
-- url     : https://prove2.me/theorems/69b947d3-b24e-4576-8651-3677b736a8fe
-- title:
--   Weighted Global Cover Scale: global representation eventually
-- statement:
--   The Weighted Global Cover Scale construction uses the global representation eventually property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L254-L259
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L254-L259

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

theorem ThreeSum.WeightedGlobalCoverScale.global_representation_eventually (c d a : ℕ) (r : ℕ → ℕ)
    (hradix : ∀ᶠ n : ℕ in Filter.atTop, prime (scale 40000000000 c d)^(r n) ≤ a*n^3) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((localFactor 40000000000 c d)^(r n) : ℝ) ≤ (n : ℝ)^(1/10000000000 : ℝ) := by sorry

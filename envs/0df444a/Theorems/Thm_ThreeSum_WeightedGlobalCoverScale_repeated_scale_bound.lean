-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_repeated_scale_bound
-- name    : ThreeSum.WeightedGlobalCoverScale.repeated_scale_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:59:03.265022+00:00
-- url     : https://prove2.me/theorems/61565212-612c-45a2-bf3e-d2ecc10a46dc
-- title:
--   Weighted Global Cover Scale: repeated scale bound
-- statement:
--   The Weighted Global Cover Scale construction uses the repeated scale bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L227-L230
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L227-L230

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

theorem ThreeSum.WeightedGlobalCoverScale.repeated_scale_bound (C c d r : ℕ) (hC : 0 < C) :
    (localFactor C c d^r)^C ≤ prime (scale C c d)^r := by sorry

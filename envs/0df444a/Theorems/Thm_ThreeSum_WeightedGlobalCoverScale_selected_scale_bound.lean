-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_selected_scale_bound
-- name    : ThreeSum.WeightedGlobalCoverScale.selected_scale_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:59:10.873501+00:00
-- url     : https://prove2.me/theorems/d6f4007f-f377-45e3-afce-354a5901908a
-- title:
--   Weighted Global Cover Scale: selected scale bound
-- statement:
--   Every polynomial carry factor and both repeated cover factors fit an
--   arbitrarily small reciprocal exponent, for a single fixed exact block.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L178-L219
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCoverScale.lean#L178-L219

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

theorem ThreeSum.WeightedGlobalCoverScale.selected_scale_bound (C c d : ℕ) (hC : 0 < C) :
    ((c*(fixedLength (scale C c d)+1)^d)*
      (frequencyFactor (scale C c d)*(Nat.log2 (prime (scale C c d)^2)+1))*
      rawThreshold (prime (scale C c d)) (sourceCap (scale C c d) (prime (scale C c d)))
        (momentOrder C))^C ≤ prime (scale C c d) := by sorry

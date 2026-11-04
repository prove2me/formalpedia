-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverScale_selected_scale_bound
-- name    : ThreeSum.TernaryCoverScale.selected_scale_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:50:53.16237+00:00
-- url     : https://prove2.me/theorems/782491a5-bff4-46fb-a9b8-80030cccc329
-- title:
--   Ternary Cover Scale: selected scale bound
-- statement:
--   Every polynomial carry factor and both repeated cover factors fit an
--   arbitrarily small reciprocal exponent, for a single fixed exact block.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverScale.lean#L171-L212
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverScale.lean#L171-L212

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

theorem ThreeSum.TernaryCoverScale.selected_scale_bound (C c d : ℕ) (hC : 0 < C) :
    ((c*(fixedLength (scale C c d)+1)^d)*
      (frequencyFactor (scale C c d)*(Nat.log2 (prime (scale C c d)^2)+1))*
      rawThreshold (prime (scale C c d)) (sourceCap (scale C c d) (prime (scale C c d)))
        (momentOrder C))^C ≤ prime (scale C c d) := by sorry

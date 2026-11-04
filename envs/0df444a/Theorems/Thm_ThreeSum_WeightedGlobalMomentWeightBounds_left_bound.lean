-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalMomentWeightBounds_left_bound
-- name    : ThreeSum.WeightedGlobalMomentWeightBounds.left_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:26:12.187199+00:00
-- url     : https://prove2.me/theorems/372980eb-531e-4a3a-8002-c29d1d99ba86
-- title:
--   Weighted Global Moment Weight Bounds: left bound
-- statement:
--   The Weighted Global Moment Weight Bounds construction uses the left bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentWeightBounds.lean#L25-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentWeightBounds.lean#L25-L31

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
import Theorems.Thm_ThreeSum_LightTernaryMomentChannels_left_bound

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalMomentWeightBounds
open LightWeightedGlobalMomentChannelFactory

theorem ThreeSum.WeightedGlobalMomentWeightBounds.left_bound {U K k j : ℕ} (x : ℤ) (hx : |x|≤(U : ℤ)) (hk : k≤K) (hj : j≤k) :
    |(k.choose j : ℤ)*(-x)^j|≤(leftBound U K : ℤ) := by sorry

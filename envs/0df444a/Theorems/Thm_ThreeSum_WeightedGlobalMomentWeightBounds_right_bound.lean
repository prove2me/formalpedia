-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalMomentWeightBounds_right_bound
-- name    : ThreeSum.WeightedGlobalMomentWeightBounds.right_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:15:21.10367+00:00
-- url     : https://prove2.me/theorems/aed0c07e-80bb-4f94-b57a-e6b1727922a8
-- title:
--   Weighted Global Moment Weight Bounds: right bound
-- statement:
--   The Weighted Global Moment Weight Bounds construction uses the right bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentWeightBounds.lean#L33-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentWeightBounds.lean#L33-L38

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
import Theorems.Thm_ThreeSum_LightTernaryMomentChannels_right_bound

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalMomentWeightBounds
open LightWeightedGlobalMomentChannelFactory

theorem ThreeSum.WeightedGlobalMomentWeightBounds.right_bound {U K k j : ℕ} (x : ℤ) (hx : |x|≤(U : ℤ)) (hk : k≤K) :
    |x^(k-j)|≤(rightBound U K : ℤ) := by sorry

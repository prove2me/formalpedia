-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalMomentWeightBounds_choose_bound
-- name    : ThreeSum.WeightedGlobalMomentWeightBounds.choose_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:15:04.406092+00:00
-- url     : https://prove2.me/theorems/8497466e-96e3-406a-b51d-46e46e6a771b
-- title:
--   Weighted Global Moment Weight Bounds: choose bound
-- statement:
--   The Weighted Global Moment Weight Bounds construction uses the choose bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentWeightBounds.lean#L21-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentWeightBounds.lean#L21-L23

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalMomentWeightBounds
open LightWeightedGlobalMomentChannelFactory

theorem ThreeSum.WeightedGlobalMomentWeightBounds.choose_bound {k j K : ℕ} (hk : k≤K) : (k.choose j : ℤ)≤(2 : ℤ)^K := by sorry

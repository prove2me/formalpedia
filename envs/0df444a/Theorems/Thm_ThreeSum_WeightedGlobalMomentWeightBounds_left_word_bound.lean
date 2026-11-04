-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalMomentWeightBounds_left_word_bound
-- name    : ThreeSum.WeightedGlobalMomentWeightBounds.left_word_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:12:11.706625+00:00
-- url     : https://prove2.me/theorems/2c98e48a-cd17-4ced-9d82-44da07338e13
-- title:
--   Weighted Global Moment Weight Bounds: left word bound
-- statement:
--   The Weighted Global Moment Weight Bounds construction uses the left word bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentWeightBounds.lean#L40-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentWeightBounds.lean#L40-L48

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalMomentWeightBounds
open LightWeightedGlobalMomentChannelFactory

theorem ThreeSum.WeightedGlobalMomentWeightBounds.left_word_bound {U K k j : ℕ} (hk : k≤K) (hj : j≤k) :
    max (U : ℤ) (2*((k.choose j : ℤ)+1)*((U : ℤ)+2)^j)≤(leftWord U K : ℤ) := by sorry

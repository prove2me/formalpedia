-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalMomentWeightBounds_right_word_bound
-- name    : ThreeSum.WeightedGlobalMomentWeightBounds.right_word_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:16:47.143818+00:00
-- url     : https://prove2.me/theorems/e68ed4f1-5646-41c1-b658-4ca0eef85bcc
-- title:
--   Weighted Global Moment Weight Bounds: right word bound
-- statement:
--   The Weighted Global Moment Weight Bounds construction uses the right word bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentWeightBounds.lean#L50-L56
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryMomentWeightBounds.lean#L50-L56

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryNativeMomentBounds
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_Submission_Weighted_Global_TernaryMomentWeightBounds
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalMomentWeightBounds
open LightWeightedGlobalMomentChannelFactory

theorem ThreeSum.WeightedGlobalMomentWeightBounds.right_word_bound {U K k j : ℕ} (hk : k≤K) :
    max (U : ℤ) (2*((U : ℤ)+1)^(k-j))≤(rightWord U K : ℤ) := by sorry

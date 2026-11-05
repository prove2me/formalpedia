-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalMomentWeightBounds_left_word_bound
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentWeightBounds.left_word_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:26:09.164629+00:00
-- url     : https://prove2.me/theorems/61f59c15-90bd-47cd-84a3-ad72dc92030e
-- title:
--   left_word_bound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryMomentWeightBounds.lean#L40-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryMomentWeightBounds.lean#L40-L48

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeMomentBounds
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentWeightBounds
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentWeightBounds
open LightWeightedGlobalMomentChannelFactory

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentWeightBounds.left_word_bound {U K k j : ℕ} (hk : k≤K) (hj : j≤k) :
    max (U : ℤ) (2*((k.choose j : ℤ)+1)*((U : ℤ)+2)^j)≤(leftWord U K : ℤ) := by sorry

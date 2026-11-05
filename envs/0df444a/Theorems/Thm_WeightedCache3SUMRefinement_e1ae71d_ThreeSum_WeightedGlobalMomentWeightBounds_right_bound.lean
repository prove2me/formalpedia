-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalMomentWeightBounds_right_bound
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentWeightBounds.right_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:24:59.916018+00:00
-- url     : https://prove2.me/theorems/ed8846cb-8654-460f-887e-ae5701b717ed
-- title:
--   right_bound
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryMomentWeightBounds.lean#L33-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryMomentWeightBounds.lean#L33-L38

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeMomentBounds
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryMomentWeightBounds
import Theorems.Thm_ThreeSum_LightTernaryMomentChannels_right_bound

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentWeightBounds
open LightWeightedGlobalMomentChannelFactory

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalMomentWeightBounds.right_bound {U K k j : ℕ} (x : ℤ) (hx : |x|≤(U : ℤ)) (hk : k≤K) :
    |x^(k-j)|≤(rightBound U K : ℤ) := by sorry

-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeTensorScore_packed_digits
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeTensorScore.packed_digits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T12:21:26.100793+00:00
-- url     : https://prove2.me/theorems/8f98fec5-cc80-4da4-a9da-3f0506bccf8b
-- title:
--   packed_digits
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeTensorScore.lean#L27-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryNativeTensorScore.lean#L27-L58

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeTensorScore
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeTensorScore
open TernaryJointType WeightedGlobalNativePairMoments
open LightWeightedGlobalTensorFactory LightTernaryPairedPolynomial
open scoped BigOperators
set_option maxHeartbeats 1500000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativeTensorScore.packed_digits {p a b c d : ℕ} (hp : 0<p)
    (ha : a<p) (hb : b<p) (hc : c<p) (hd : d<p) :
    WeightEnumeration.digit p 4 (tensorIndex p a b c d) 0=a ∧
    WeightEnumeration.digit p 4 (tensorIndex p a b c d) 1=b ∧
    WeightEnumeration.digit p 4 (tensorIndex p a b c d) 2=c ∧
    WeightEnumeration.digit p 4 (tensorIndex p a b c d) 3=d := by sorry

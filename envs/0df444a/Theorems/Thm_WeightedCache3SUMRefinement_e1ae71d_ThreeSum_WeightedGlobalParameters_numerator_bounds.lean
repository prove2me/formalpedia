-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_numerator_bounds
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters.numerator_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:11:43.815904+00:00
-- url     : https://prove2.me/theorems/fc4b9b4b-9325-4f51-969a-51ad25021c5e
-- title:
--   numerator_bounds
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalParameters.lean#L201-L213
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalParameters.lean#L201-L213

import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalParameters
import Theorems.Thm_WeightedCacheParameters_e1ae71d_numerator_bounds

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters.numerator_bounds :
    2*WeightedCacheParameters_e1ae71d.Bn<certificateExponent*WeightedCacheParameters_e1ae71d.Hn ∧
    2*WeightedCacheParameters_e1ae71d.Hn-WeightedCacheParameters_e1ae71d.Gn+2*WeightedCacheParameters_e1ae71d.Qn<certificateExponent*WeightedCacheParameters_e1ae71d.Hn ∧
    2*WeightedCacheParameters_e1ae71d.An<certificateExponent*WeightedCacheParameters_e1ae71d.Hn ∧
    WeightedCacheParameters_e1ae71d.Hn+WeightedCacheParameters_e1ae71d.Gn<certificateExponent*WeightedCacheParameters_e1ae71d.Hn ∧
    2*WeightedCacheParameters_e1ae71d.Hn-WeightedCacheParameters_e1ae71d.Gn<certificateExponent*WeightedCacheParameters_e1ae71d.Hn := by sorry

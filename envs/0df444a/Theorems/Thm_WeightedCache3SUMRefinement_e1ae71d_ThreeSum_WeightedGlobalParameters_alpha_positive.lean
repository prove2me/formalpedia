-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_alpha_positive
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters.alpha_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:06:21.500828+00:00
-- url     : https://prove2.me/theorems/058bfb42-f8ae-44ca-979a-a6ba7bc11c1e
-- title:
--   alpha_positive
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalParameters.lean#L96-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalParameters.lean#L96-L97

import Definitions.Def_Submission_Weighted_Parameters_w3sum_e1ae71d
import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalParameters
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters.alpha_positive : 0 < alpha0 ∧ 0 < alpha1 ∧ 0 < alpha2 := by sorry

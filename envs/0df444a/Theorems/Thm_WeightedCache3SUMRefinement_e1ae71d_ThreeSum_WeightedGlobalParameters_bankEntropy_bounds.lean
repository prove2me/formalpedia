-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_bankEntropy_bounds
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters.bankEntropy_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:06:15.534496+00:00
-- url     : https://prove2.me/theorems/65411a34-fddc-44ea-9409-b473c9cf455d
-- title:
--   bankEntropy_bounds
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalParameters.lean#L75-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalParameters.lean#L75-L82

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters.bankEntropy_bounds : (78202/100000 : ℝ)≤bankEntropy ∧ bankEntropy≤(78203/100000 : ℝ) := by sorry

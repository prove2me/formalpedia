-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalParameters_ledger_individual_bounds
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters.ledger_individual_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:05:57.835463+00:00
-- url     : https://prove2.me/theorems/85720793-60ae-4218-9e40-569a755b1fbb
-- title:
--   ledger_individual_bounds
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalParameters.lean#L215-L238
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/GlobalParameters.lean#L215-L238

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalParameters.ledger_individual_bounds :
    2*bankEntropy/Hpi<certificateExponent ∧
    2-partitionEntropy/Hpi+2*queryEntropy/Hpi<certificateExponent ∧
    2*Halpha/Hpi<certificateExponent ∧
    1+partitionEntropy/Hpi<certificateExponent ∧
    2-partitionEntropy/Hpi<certificateExponent := by sorry

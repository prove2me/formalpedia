-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalEntropyRates_actual_prime_rate
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates.actual_prime_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:25:22.375263+00:00
-- url     : https://prove2.me/theorems/ad3a57ae-3e7e-48ad-92e1-88381772a20b
-- title:
--   actual_prime_rate
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryEntropyRates.lean#L185-L196
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryEntropyRates.lean#L185-L196

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryEntropyRates
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters WeightedGlobalCoverScale
set_option maxRecDepth 10000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates.actual_prime_rate :
    Tendsto primeRate atTop (𝓝 ((WeightedGlobalParameters.Hpi+WeightedGlobalParameters.partitionEntropy)/2)) := by sorry

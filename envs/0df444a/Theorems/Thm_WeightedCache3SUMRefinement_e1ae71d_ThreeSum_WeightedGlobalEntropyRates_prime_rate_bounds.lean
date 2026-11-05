-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalEntropyRates_prime_rate_bounds
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates.prime_rate_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:25:33.483964+00:00
-- url     : https://prove2.me/theorems/9a0a8451-fc7a-4f76-b0d8-b0d15a4e1b81
-- title:
--   prime_rate_bounds
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryEntropyRates.lean#L141-L169
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/Global/TernaryEntropyRates.lean#L141-L169

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

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates.prime_rate_bounds {m : ℕ} (hm : 0 < m) :
    (outputRate m+WeightedGlobalParameters.partitionEntropy)/2 ≤ primeRate m ∧
    primeRate m ≤ (outputRate m+WeightedGlobalParameters.partitionEntropy)/2+
      Real.log 16/(2*((fixedLength m : ℝ)*Real.log 2)) := by sorry

-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_prime_rate_bounds
-- name    : ThreeSum.WeightedGlobalEntropyRates.prime_rate_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:02:06.216345+00:00
-- url     : https://prove2.me/theorems/cd1fa605-43ea-42e7-a26d-38baa83f4814
-- title:
--   Weighted Global Entropy Rates: prime rate bounds
-- statement:
--   The Weighted Global Entropy Rates construction uses the prime rate bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L141-L169
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L141-L169

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_GlobalParameters
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters WeightedGlobalCoverScale
set_option maxRecDepth 10000

theorem ThreeSum.WeightedGlobalEntropyRates.prime_rate_bounds {m : ℕ} (hm : 0 < m) :
    (outputRate m+WeightedGlobalParameters.partitionEntropy)/2 ≤ primeRate m ∧
    primeRate m ≤ (outputRate m+WeightedGlobalParameters.partitionEntropy)/2+
      Real.log 16/(2*((fixedLength m : ℝ)*Real.log 2)) := by sorry

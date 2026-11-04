-- Prove2me | Theorems.Thm_ThreeSum_TernaryEntropyRates_prime_rate_bounds
-- name    : ThreeSum.TernaryEntropyRates.prime_rate_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:53:13.512621+00:00
-- url     : https://prove2.me/theorems/52d645f6-01df-4e55-abe1-8e97c441d7cd
-- title:
--   Ternary Entropy Rates: prime rate bounds
-- statement:
--   The Ternary Entropy Rates construction uses the prime rate bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L135-L163
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L135-L163

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_Submission_ThreeSum_TernaryEntropyRates
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal TernaryLocalParameters TernaryCoverScale
set_option maxRecDepth 10000

theorem ThreeSum.TernaryEntropyRates.prime_rate_bounds {m : ℕ} (hm : 0 < m) :
    (outputRate m+TernaryParameters.partitionEntropy)/2 ≤ primeRate m ∧
    primeRate m ≤ (outputRate m+TernaryParameters.partitionEntropy)/2+
      Real.log 16/(2*((fixedLength m : ℝ)*Real.log 2)) := by sorry

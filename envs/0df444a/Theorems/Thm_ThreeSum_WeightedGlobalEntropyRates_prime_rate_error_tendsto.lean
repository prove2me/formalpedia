-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_prime_rate_error_tendsto
-- name    : ThreeSum.WeightedGlobalEntropyRates.prime_rate_error_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:01:35.645211+00:00
-- url     : https://prove2.me/theorems/e7e9e968-006c-45e6-b857-94b3f31b7f24
-- title:
--   Weighted Global Entropy Rates: prime rate error tendsto
-- statement:
--   The Weighted Global Entropy Rates construction uses the prime rate error tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L171-L183
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L171-L183

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

theorem ThreeSum.WeightedGlobalEntropyRates.prime_rate_error_tendsto :
    Tendsto (fun m : ℕ => Real.log 16/(2*((fixedLength m : ℝ)*Real.log 2)))
      atTop (𝓝 0) := by sorry

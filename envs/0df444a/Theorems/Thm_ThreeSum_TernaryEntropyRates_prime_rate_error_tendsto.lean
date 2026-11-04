-- Prove2me | Theorems.Thm_ThreeSum_TernaryEntropyRates_prime_rate_error_tendsto
-- name    : ThreeSum.TernaryEntropyRates.prime_rate_error_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:53:17.810969+00:00
-- url     : https://prove2.me/theorems/3ae82211-ab43-431a-be9d-31d8444e5b1a
-- title:
--   Ternary Entropy Rates: prime rate error tendsto
-- statement:
--   The Ternary Entropy Rates construction uses the prime rate error tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L165-L177
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L165-L177

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

theorem ThreeSum.TernaryEntropyRates.prime_rate_error_tendsto :
    Tendsto (fun m : ℕ => Real.log 16/(2*((fixedLength m : ℝ)*Real.log 2)))
      atTop (𝓝 0) := by sorry

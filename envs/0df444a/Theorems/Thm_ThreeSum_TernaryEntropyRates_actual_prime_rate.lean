-- Prove2me | Theorems.Thm_ThreeSum_TernaryEntropyRates_actual_prime_rate
-- name    : ThreeSum.TernaryEntropyRates.actual_prime_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:43:07.220718+00:00
-- url     : https://prove2.me/theorems/295594cc-0014-4583-a58a-3450b517e03d
-- title:
--   Ternary Entropy Rates: actual prime rate
-- statement:
--   The Ternary Entropy Rates construction uses the actual prime rate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L179-L190
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L179-L190

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

theorem ThreeSum.TernaryEntropyRates.actual_prime_rate :
    Tendsto primeRate atTop (𝓝 ((TernaryParameters.Hpi+TernaryParameters.partitionEntropy)/2)) := by sorry

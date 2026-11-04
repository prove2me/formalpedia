-- Prove2me | Theorems.Thm_ThreeSum_TernaryEntropyRates_actual_endpoint_count
-- name    : ThreeSum.TernaryEntropyRates.actual_endpoint_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:51:01.16942+00:00
-- url     : https://prove2.me/theorems/28d2046e-711d-4838-8237-593eed727b3e
-- title:
--   Ternary Entropy Rates: actual endpoint count
-- statement:
--   The Ternary Entropy Rates construction uses the actual endpoint count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L98-L104
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L98-L104

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

theorem ThreeSum.TernaryEntropyRates.actual_endpoint_count (m : ℕ) :
    endpointSize m=typeCount 100000000 8908493 978268 m := by sorry

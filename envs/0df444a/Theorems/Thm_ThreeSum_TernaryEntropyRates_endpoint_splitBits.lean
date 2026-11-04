-- Prove2me | Theorems.Thm_ThreeSum_TernaryEntropyRates_endpoint_splitBits
-- name    : ThreeSum.TernaryEntropyRates.endpoint_splitBits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:51:40.639977+00:00
-- url     : https://prove2.me/theorems/99670fd3-db59-4ead-9da6-6a0fa274b2b2
-- title:
--   Ternary Entropy Rates: endpoint split Bits
-- statement:
--   The Ternary Entropy Rates construction uses the endpoint split Bits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L64-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L64-L69

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

theorem ThreeSum.TernaryEntropyRates.endpoint_splitBits : splitBits 100000000 8908493 978268 = TernaryParameters.Halpha := by sorry

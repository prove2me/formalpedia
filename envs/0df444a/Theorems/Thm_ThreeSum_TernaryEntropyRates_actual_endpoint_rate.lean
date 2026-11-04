-- Prove2me | Theorems.Thm_ThreeSum_TernaryEntropyRates_actual_endpoint_rate
-- name    : ThreeSum.TernaryEntropyRates.actual_endpoint_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:51:59.191706+00:00
-- url     : https://prove2.me/theorems/16d89876-9dca-43a4-b653-da28e6bd207c
-- title:
--   Ternary Entropy Rates: actual endpoint rate
-- statement:
--   The Ternary Entropy Rates construction uses the actual endpoint rate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L114-L116
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L114-L116

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

theorem ThreeSum.TernaryEntropyRates.actual_endpoint_rate : Tendsto endpointRate atTop (𝓝 TernaryParameters.Halpha) := by sorry

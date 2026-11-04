-- Prove2me | Theorems.Thm_ThreeSum_TernaryEntropyRates_output_splitBits
-- name    : ThreeSum.TernaryEntropyRates.output_splitBits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:51:37.212048+00:00
-- url     : https://prove2.me/theorems/c18ca0d0-1fe9-493c-bde6-aaff867590d9
-- title:
--   Ternary Entropy Rates: output split Bits
-- statement:
--   The Ternary Entropy Rates construction uses the output split Bits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L57-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L57-L62

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

theorem ThreeSum.TernaryEntropyRates.output_splitBits : splitBits 100000000 15860450 2934804 = TernaryParameters.Hpi := by sorry

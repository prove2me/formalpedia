-- Prove2me | Theorems.Thm_ThreeSum_TernaryEntropyRates_endpoint_formula_rate
-- name    : ThreeSum.TernaryEntropyRates.endpoint_formula_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:51:37.611553+00:00
-- url     : https://prove2.me/theorems/33f790a7-6933-4345-91fa-bf628558de53
-- title:
--   Ternary Entropy Rates: endpoint formula rate
-- statement:
--   The Ternary Entropy Rates construction uses the endpoint formula rate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L78-L83
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L78-L83

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

theorem ThreeSum.TernaryEntropyRates.endpoint_formula_rate :
    Tendsto (fun m : ℕ => Real.log (typeCount 100000000 8908493 978268 m : ℝ)/
      (((100000000*m : ℕ) : ℝ)*Real.log 2)) atTop (𝓝 TernaryParameters.Halpha) := by sorry

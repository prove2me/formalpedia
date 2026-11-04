-- Prove2me | Theorems.Thm_ThreeSum_TernaryEntropyRates_entropy_split
-- name    : ThreeSum.TernaryEntropyRates.entropy_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:01:00.723775+00:00
-- url     : https://prove2.me/theorems/e9ba74d3-660e-4b13-8b50-920e43b53d6c
-- title:
--   Ternary Entropy Rates: entropy split
-- statement:
--   The Ternary Entropy Rates construction uses the entropy split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L14-L24
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEntropyRates.lean#L14-L24

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

theorem ThreeSum.TernaryEntropyRates.entropy_split {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hs : a+b+c=1) :
    Real.binEntropy c+(1-c)*Real.binEntropy (b/(1-c)) =
      -a*Real.log a-b*Real.log b-c*Real.log c := by sorry

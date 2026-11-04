-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_entropy_split
-- name    : ThreeSum.WeightedGlobalEntropyRates.entropy_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:01:04.940197+00:00
-- url     : https://prove2.me/theorems/3c10eaf1-83dc-48a9-bc9b-290a58d0d30d
-- title:
--   Weighted Global Entropy Rates: entropy split
-- statement:
--   The Weighted Global Entropy Rates construction uses the entropy split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L21-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L21-L31

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

theorem ThreeSum.WeightedGlobalEntropyRates.entropy_split {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hs : a+b+c=1) :
    Real.binEntropy c+(1-c)*Real.binEntropy (b/(1-c)) =
      -a*Real.log a-b*Real.log b-c*Real.log c := by sorry

-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_typeCount_pos
-- name    : ThreeSum.WeightedGlobalEntropyRates.typeCount_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:44:36.315254+00:00
-- url     : https://prove2.me/theorems/acd974a8-bcd3-4624-8a65-17044a3b7d64
-- title:
--   Weighted Global Entropy Rates: type Count pos
-- statement:
--   The Weighted Global Entropy Rates construction uses the type Count pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L36-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryEntropyRates.lean#L36-L40

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

theorem ThreeSum.WeightedGlobalEntropyRates.typeCount_pos {N r1 r2 : ℕ} (h1 : r1+r2 ≤ N) (m : ℕ) :
    0 < typeCount N r1 r2 m := by sorry

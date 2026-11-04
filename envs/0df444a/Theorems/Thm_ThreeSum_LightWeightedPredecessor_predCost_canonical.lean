-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedPredecessor_predCost_canonical
-- name    : ThreeSum.LightWeightedPredecessor.predCost_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:48:31.11796+00:00
-- url     : https://prove2.me/theorems/0c5a02c5-2a79-4171-90bb-117df64a2744
-- title:
--   Light Weighted Predecessor: pred Cost canonical
-- statement:
--   The Light Weighted Predecessor construction uses the pred Cost canonical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Predecessor.lean#L240-L244
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Predecessor.lean#L240-L244

import Definitions.Def_Submission_ThreeSum_LightTernaryRankTable
import Definitions.Def_Submission_Weighted_LightCost
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_Weighted_Predecessor
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedPredecessor
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryCodeSemantics
open ThreeSum.TernaryEuler
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedPredecessor.predCost_canonical {N : ℕ} (R : TritWord N) (i : Fin N)
    (hi : 0<(R i).val) :
    predCost N (low i) (high i) (address R)=WeightedBankEnumeration.cacheCost (predecessor R i) := by sorry

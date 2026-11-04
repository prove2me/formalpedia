-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedPredecessor_code_canonical
-- name    : ThreeSum.LightWeightedPredecessor.code_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:48:38.352691+00:00
-- url     : https://prove2.me/theorems/3d3aa6ff-aa15-4b4e-91d8-15e0780ee662
-- title:
--   Light Weighted Predecessor: code canonical
-- statement:
--   The Light Weighted Predecessor construction uses the code canonical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Predecessor.lean#L45-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Predecessor.lean#L45-L70

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

theorem ThreeSum.LightWeightedPredecessor.code_canonical {N : ℕ} (w : TritWord N) (i : Fin N) (hi : 0<(w i).val) :
    code N (low i) (high i) (address w)=address (predecessor w i) := by sorry

-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedPredecessor_code_lt
-- name    : ThreeSum.LightWeightedPredecessor.code_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:57:01.671682+00:00
-- url     : https://prove2.me/theorems/d2cd8de1-6bc3-477c-9c0c-6a3493eb79b1
-- title:
--   Light Weighted Predecessor: code lt
-- statement:
--   The Light Weighted Predecessor construction uses the code lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Predecessor.lean#L37-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Predecessor.lean#L37-L43

import Definitions.Def_Submission_ThreeSum_LightTernaryRankTable
import Definitions.Def_Submission_Weighted_LightCost
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_Weighted_Predecessor
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low
import Theorems.Thm_ThreeSum_TernaryAddresses_code_lt
import Theorems.Thm_ThreeSum_WeightedAddresses_code_lt

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedPredecessor
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryCodeSemantics
open ThreeSum.TernaryEuler
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedPredecessor.code_lt {N low high m : ℕ} (hm : m<2^(2*N)) :
    code N low high m<2^(2*N) := by sorry

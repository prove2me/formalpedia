-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPredecessor_code_lt
-- name    : ThreeSum.LightTernaryPredecessor.code_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:58:39.423212+00:00
-- url     : https://prove2.me/theorems/4d9a0bd5-31f5-48d4-8aa4-ab34500584bf
-- title:
--   Light Ternary Predecessor: code lt
-- statement:
--   The Light Ternary Predecessor construction uses the code lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPredecessor.lean#L31-L37
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPredecessor.lean#L31-L37

import Definitions.Def_Submission_ThreeSum_LightTernaryRankTable
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessor
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low
import Theorems.Thm_ThreeSum_TernaryAddresses_code_lt

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryPredecessor
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryCodeSemantics
open ThreeSum.TernaryEuler
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

theorem ThreeSum.LightTernaryPredecessor.code_lt {N low high m : ℕ} (hm : m<2^(2*N)) :
    code N low high m<2^(2*N) := by sorry

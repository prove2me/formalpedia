-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryPredecessor_code_canonical
-- name    : ThreeSum.LightTernaryPredecessor.code_canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:50:17.6213+00:00
-- url     : https://prove2.me/theorems/589ef4f4-5dee-4cad-84cb-36d9ad704ff8
-- title:
--   Light Ternary Predecessor: code canonical
-- statement:
--   The Light Ternary Predecessor construction uses the code canonical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPredecessor.lean#L39-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPredecessor.lean#L39-L64

import Definitions.Def_Submission_ThreeSum_LightTernaryRankTable
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessor
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryPredecessor
open Light ThreeSum.LightSubsetAddress ThreeSum.MaskErase
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryCodeSemantics
open ThreeSum.TernaryEuler
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

theorem ThreeSum.LightTernaryPredecessor.code_canonical {N : ℕ} (w : TritWord N) (i : Fin N) (hi : 0<(w i).val) :
    code N (low i) (high i) (address w)=address (predecessor w i) := by sorry

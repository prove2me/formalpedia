-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalEuler_bank_index_correct
-- name    : ThreeSum.TernaryPhysicalEuler.bank_index_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:31:57.976555+00:00
-- url     : https://prove2.me/theorems/ee4893ce-a34a-482d-bc91-fcdf618c3f6e
-- title:
--   Ternary Physical Euler: bank index correct
-- statement:
--   The Ternary Physical Euler construction uses the bank index correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalEuler.lean#L214-L235
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalEuler.lean#L214-L235

import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 3000000

theorem ThreeSum.TernaryPhysicalEuler.bank_index_correct {N nb T : ℕ} (bankWords : ℕ → TritWord N)
    (hbank : ∀ W, rank W≤T → ∃ j<nb, bankWords j=W)
    (R : TritWord N) (i : ℕ) (hi : i<N)
    (hdigit : LightTernaryPredecessor.digit N (LightTernaryEulerMetadata.lowAt N i)
      (LightTernaryEulerMetadata.highAt N i) (address R)≠0)
    (hrank : LightTernaryPredecessor.predRank N (LightTernaryEulerMetadata.lowAt N i)
      (LightTernaryEulerMetadata.highAt N i) (address R)≤T) :
    predecessorOrdinal bankWords nb R i<nb ∧
      address (bankWords (predecessorOrdinal bankWords nb R i))=
        LightTernaryPredecessor.code N (LightTernaryEulerMetadata.lowAt N i)
          (LightTernaryEulerMetadata.highAt N i) (address R) := by sorry

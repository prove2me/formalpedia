-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalEuler_near_index_correct
-- name    : ThreeSum.TernaryPhysicalEuler.near_index_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:31:51.420599+00:00
-- url     : https://prove2.me/theorems/030a44ee-139a-47de-a458-352e51441d72
-- title:
--   Ternary Physical Euler: near index correct
-- statement:
--   The Ternary Physical Euler construction uses the near index correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalEuler.lean#L237-L259
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalEuler.lean#L237-L259

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

theorem ThreeSum.TernaryPhysicalEuler.near_index_correct {N nn T : ℕ} (Q R : TritWord N)
    (nearWords : ℕ → TritWord N)
    (hnear : ∀ W, Below W Q → T<rank W → ∃ j<nn, nearWords j=W)
    (hRQ : Below R Q) (i : ℕ) (hi : i<N)
    (hdigit : LightTernaryPredecessor.digit N (LightTernaryEulerMetadata.lowAt N i)
      (LightTernaryEulerMetadata.highAt N i) (address R)≠0)
    (hrank : T<LightTernaryPredecessor.predRank N (LightTernaryEulerMetadata.lowAt N i)
      (LightTernaryEulerMetadata.highAt N i) (address R)) :
    predecessorOrdinal nearWords nn R i<nn ∧
      address (nearWords (predecessorOrdinal nearWords nn R i))=
        LightTernaryPredecessor.code N (LightTernaryEulerMetadata.lowAt N i)
          (LightTernaryEulerMetadata.highAt N i) (address R) := by sorry

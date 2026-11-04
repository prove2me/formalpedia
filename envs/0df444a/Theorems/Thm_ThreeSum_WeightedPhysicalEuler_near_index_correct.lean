-- Prove2me | Theorems.Thm_ThreeSum_WeightedPhysicalEuler_near_index_correct
-- name    : ThreeSum.WeightedPhysicalEuler.near_index_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:23:57.14538+00:00
-- url     : https://prove2.me/theorems/9bb81c52-41e9-4f59-b0e1-249b91100330
-- title:
--   Weighted Physical Euler: near index correct
-- statement:
--   The Weighted Physical Euler construction uses the near index correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PhysicalEuler.lean#L243-L265
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PhysicalEuler.lean#L243-L265

import Definitions.Def_Submission_Weighted_EulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_Submission_Weighted_PhysicalEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
open ThreeSum.WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 3000000

theorem ThreeSum.WeightedPhysicalEuler.near_index_correct {N nn T : ℕ} (Q R : TritWord N)
    (nearWords : ℕ → TritWord N)
    (hnear : ∀ W, Below W Q → T<cacheCost W → ∃ j<nn, nearWords j=W)
    (hRQ : Below R Q) (i : ℕ) (hi : i<N)
    (hdigit : LightWeightedPredecessor.digit N (LightWeightedEulerMetadata.lowAt N i)
      (LightWeightedEulerMetadata.highAt N i) (address R)≠0)
    (hrank : T<LightWeightedPredecessor.predCost N (LightWeightedEulerMetadata.lowAt N i)
      (LightWeightedEulerMetadata.highAt N i) (address R)) :
    predecessorOrdinal nearWords nn R i<nn ∧
      address (nearWords (predecessorOrdinal nearWords nn R i))=
        LightWeightedPredecessor.code N (LightWeightedEulerMetadata.lowAt N i)
          (LightWeightedEulerMetadata.highAt N i) (address R) := by sorry

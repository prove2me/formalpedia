-- Prove2me | Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedPhysicalEuler_near_index_correct
-- name    : WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPhysicalEuler.near_index_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T10:12:51.647381+00:00
-- url     : https://prove2.me/theorems/8bb8290b-063a-43a1-96bf-c7c6db9d6b1e
-- title:
--   near_index_correct
-- statement:
--   Refined weighted-cache 3SUM lemma. Its formal statement preserves the complete source hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PhysicalEuler.lean#L243-L265
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/e1ae71db2231f172c6541820e2ce0a54aa14fc64/Submission/Weighted/PhysicalEuler.lean#L243-L265

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_EulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PhysicalEuler
set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
open ThreeSum.WeightedBankEnumeration (cacheCost)
set_option maxHeartbeats 3000000

theorem WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedPhysicalEuler.near_index_correct {N nn T : ℕ} (Q R : TritWord N)
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

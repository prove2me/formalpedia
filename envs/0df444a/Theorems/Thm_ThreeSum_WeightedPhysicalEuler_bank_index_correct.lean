-- Prove2me | Theorems.Thm_ThreeSum_WeightedPhysicalEuler_bank_index_correct
-- name    : ThreeSum.WeightedPhysicalEuler.bank_index_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:23:49.564863+00:00
-- url     : https://prove2.me/theorems/1092e72c-14d6-404b-9292-ee5d5b1e48a3
-- title:
--   Weighted Physical Euler: bank index correct
-- statement:
--   The Weighted Physical Euler construction uses the bank index correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PhysicalEuler.lean#L220-L241
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PhysicalEuler.lean#L220-L241

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

theorem ThreeSum.WeightedPhysicalEuler.bank_index_correct {N nb T : ℕ} (bankWords : ℕ → TritWord N)
    (hbank : ∀ W, cacheCost W≤T → ∃ j<nb, bankWords j=W)
    (R : TritWord N) (i : ℕ) (hi : i<N)
    (hdigit : LightWeightedPredecessor.digit N (LightWeightedEulerMetadata.lowAt N i)
      (LightWeightedEulerMetadata.highAt N i) (address R)≠0)
    (hrank : LightWeightedPredecessor.predCost N (LightWeightedEulerMetadata.lowAt N i)
      (LightWeightedEulerMetadata.highAt N i) (address R)≤T) :
    predecessorOrdinal bankWords nb R i<nb ∧
      address (bankWords (predecessorOrdinal bankWords nb R i))=
        LightWeightedPredecessor.code N (LightWeightedEulerMetadata.lowAt N i)
          (LightWeightedEulerMetadata.highAt N i) (address R) := by sorry

-- Prove2me | Theorems.Thm_ThreeSum_WeightedPhysicalEuler_positive_read
-- name    : ThreeSum.WeightedPhysicalEuler.positive_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:23:27.926196+00:00
-- url     : https://prove2.me/theorems/8ac1a0a0-9271-424c-8648-ebdf46f12ac9
-- title:
--   Weighted Physical Euler: positive read
-- statement:
--   Every positive read is exactly the canonical predecessor.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PhysicalEuler.lean#L98-L111
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PhysicalEuler.lean#L98-L111

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

theorem ThreeSum.WeightedPhysicalEuler.positive_read {N nb nn T bv nv : ℕ} (R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (hsep : bv+nb≤nv)
    (hbank : ∀ W, cacheCost W≤T → ∃ j<nb, bankWords j=W)
    (hnear : ∀ i : Fin N, T<cacheCost (predecessor R i) → ∃ j<nn, nearWords j=predecessor R i)
    (i : Fin N) (hi : 0<(R i).val) :
    physicalWord bankWords nearWords bv nv (rowKey R bankWords nearWords nb nn T bv nv i.val)=
      predecessor R i := by sorry

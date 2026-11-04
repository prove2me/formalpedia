-- Prove2me | Theorems.Thm_ThreeSum_WeightedPhysicalEuler_rowKey_bank_read
-- name    : ThreeSum.WeightedPhysicalEuler.rowKey_bank_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:24:00.43461+00:00
-- url     : https://prove2.me/theorems/b3abfb45-b1ce-4c26-b9d6-385013552aac
-- title:
--   Weighted Physical Euler: row Key bank read
-- statement:
--   Exact original bank reads, including the dummy read, suffice for all
--   predecessor reads that lie before the near destination.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PhysicalEuler.lean#L190-L213
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/PhysicalEuler.lean#L190-L213

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

theorem ThreeSum.WeightedPhysicalEuler.rowKey_bank_read {N nb nn T bv nv : ℕ} (Q R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (F : TritWord N → ℤ) (μ : ℕ → ℤ)
    (hsep : bv+nb≤nv) (hnb : 0<nb)
    (hbank : ∀ W, cacheCost W≤T → ∃ j<nb, bankWords j=W)
    (hnear : ∀ W, Below W Q → T<cacheCost W → ∃ j<nn, nearWords j=W)
    (hRQ : Below R Q)
    (hread : ∀ j<nb, μ (bv+j)=F (bankWords j)) (i : Fin N)
    (hk : rowKey R bankWords nearWords nb nn T bv nv i.val<nv) :
    ∃ j<nb, rowKey R bankWords nearWords nb nn T bv nv i.val=bv+j ∧
      μ (rowKey R bankWords nearWords nb nn T bv nv i.val)=
        physicalValue F bankWords nearWords bv nv (rowKey R bankWords nearWords nb nn T bv nv i.val) := by sorry

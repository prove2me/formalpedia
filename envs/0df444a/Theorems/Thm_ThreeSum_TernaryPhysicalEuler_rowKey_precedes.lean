-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalEuler_rowKey_precedes
-- name    : ThreeSum.TernaryPhysicalEuler.rowKey_precedes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:59:58.586483+00:00
-- url     : https://prove2.me/theorems/c2dee693-6614-4f59-baf1-bda3930c6f6b
-- title:
--   Ternary Physical Euler: row Key precedes
-- statement:
--   Every metadata address is inside an initialized bank or a strictly earlier
--   near rank. In particular a zero-weight read is still a real initialized read.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalEuler.lean#L143-L162
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalEuler.lean#L143-L162

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

theorem ThreeSum.TernaryPhysicalEuler.rowKey_precedes {N nb nn T bv nv : ℕ} (Q R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (hsep : bv+nb≤nv) (hnb : 0<nb)
    (hbank : ∀ W, rank W≤T → ∃ j<nb, bankWords j=W)
    (hnear : ∀ W, Below W Q → T<rank W → ∃ j<nn, nearWords j=W)
    (hRQ : Below R Q) (i : Fin N) :
    rowKey R bankWords nearWords nb nn T bv nv i.val<nv ∨
      ∃ j<nn, rowKey R bankWords nearWords nb nn T bv nv i.val=nv+j ∧
        rank (nearWords j)<rank R := by sorry

-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalEuler_positive_read
-- name    : ThreeSum.TernaryPhysicalEuler.positive_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:30:17.891665+00:00
-- url     : https://prove2.me/theorems/b6475bd9-6bdd-46fa-a5dd-ad3d9b473ab9
-- title:
--   Ternary Physical Euler: positive read
-- statement:
--   Every positive read is exactly the canonical predecessor.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalEuler.lean#L92-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalEuler.lean#L92-L105

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

theorem ThreeSum.TernaryPhysicalEuler.positive_read {N nb nn T bv nv : ℕ} (R : TritWord N)
    (bankWords nearWords : ℕ → TritWord N) (hsep : bv+nb≤nv)
    (hbank : ∀ W, rank W≤T → ∃ j<nb, bankWords j=W)
    (hnear : ∀ i : Fin N, T<rank (predecessor R i) → ∃ j<nn, nearWords j=predecessor R i)
    (i : Fin N) (hi : 0<(R i).val) :
    physicalWord bankWords nearWords bv nv (rowKey R bankWords nearWords nb nn T bv nv i.val)=
      predecessor R i := by sorry

-- Prove2me | Theorems.Thm_ThreeSum_TernaryPhysicalEuler_near_predecessor_present
-- name    : ThreeSum.TernaryPhysicalEuler.near_predecessor_present
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:58:00.406389+00:00
-- url     : https://prove2.me/theorems/3c041d16-4d94-46ac-b5b7-d525f3b55233
-- title:
--   Ternary Physical Euler: near predecessor present
-- statement:
--   A predecessor reached outside the bank is present in the same near segment.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalEuler.lean#L134-L139
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPhysicalEuler.lean#L134-L139

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

theorem ThreeSum.TernaryPhysicalEuler.near_predecessor_present {N nn T : ℕ} (Q R : TritWord N)
    (nearWords : ℕ → TritWord N)
    (hnear : ∀ W, Below W Q → T<rank W → ∃ j<nn, nearWords j=W)
    (hRQ : Below R Q) (i : Fin N) (hr : T<rank (predecessor R i)) :
    ∃ j<nn, nearWords j=predecessor R i := by sorry

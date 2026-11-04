-- Prove2me | Theorems.Thm_ThreeSum_TernaryPartialEuler_stageSum_euler_safe
-- name    : ThreeSum.TernaryPartialEuler.stageSum_euler_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:30.963332+00:00
-- url     : https://prove2.me/theorems/0985c9ef-86b6-4952-890e-85b2d63b2b7b
-- title:
--   Ternary Partial Euler: stage Sum euler safe
-- statement:
--   Zero-weight coordinates may use an arbitrary safe bank address.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartialEuler.lean#L120-L126
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartialEuler.lean#L120-L126

import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPartialEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryTransform
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryPartialEuler.stageSum_euler_safe {N h : ℕ} (S : Finset (Fin N)) (f : TritWord N→ℤ)
    (hf : ∀ A, f A≠0 → rank A=h) (R dummy : TritWord N) :
    (∑ i : Fin N, restrictedWeight S R i*
        stageSum S f (safePredecessor S R dummy i))=
      ((rank R : ℤ)-(h : ℤ))*stageSum S f R := by sorry

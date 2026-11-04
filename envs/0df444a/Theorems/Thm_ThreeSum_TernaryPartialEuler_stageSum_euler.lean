-- Prove2me | Theorems.Thm_ThreeSum_TernaryPartialEuler_stageSum_euler
-- name    : ThreeSum.TernaryPartialEuler.stageSum_euler
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:27.595348+00:00
-- url     : https://prove2.me/theorems/3b3d6b61-a310-4bd3-a093-799aeb3cf61f
-- title:
--   Ternary Partial Euler: stage Sum euler
-- statement:
--   Only the coordinates still transformed participate in the Euler numerator.
--   The denominator retains the rank of the complete word, including frozen coordinates.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartialEuler.lean#L81-L93
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartialEuler.lean#L81-L93

import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPartialEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryTransform
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryPartialEuler.stageSum_euler {N h : ℕ} (S : Finset (Fin N)) (f : TritWord N→ℤ)
    (hf : ∀ A, f A≠0 → rank A=h) (R : TritWord N) :
    (∑ i∈S, (R i).val*stageSum S f (predecessor R i))=
      ((rank R : ℤ)-(h : ℤ))*stageSum S f R := by sorry

-- Prove2me | Theorems.Thm_ThreeSum_TernaryPartialEuler_stageSum_euler_general
-- name    : ThreeSum.TernaryPartialEuler.stageSum_euler_general
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:29.254845+00:00
-- url     : https://prove2.me/theorems/15123f46-003d-455f-87db-48dba70a35f6
-- title:
--   Ternary Partial Euler: stage Sum euler general
-- statement:
--   The Ternary Partial Euler construction uses the stage Sum euler general property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartialEuler.lean#L68-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartialEuler.lean#L68-L77

import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPartialEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryTransform
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryPartialEuler.stageSum_euler_general {N : ℕ} (S : Finset (Fin N))
    (f : TritWord N→ℤ) (R : TritWord N) :
    (∑ i∈S, (R i).val*stageSum S f (predecessor R i))=
      ∑ A : TritWord N, ((rank R : ℤ)-(rank A : ℤ))*kernel S R A*f A := by sorry

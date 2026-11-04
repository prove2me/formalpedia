-- Prove2me | Theorems.Thm_ThreeSum_TernaryPartialEuler_coordinate_kernel_euler
-- name    : ThreeSum.TernaryPartialEuler.coordinate_kernel_euler
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:27.17353+00:00
-- url     : https://prove2.me/theorems/4e6c9dbd-f779-4226-8921-f2861d715b93
-- title:
--   Ternary Partial Euler: coordinate kernel euler
-- statement:
--   The Ternary Partial Euler construction uses the coordinate kernel euler property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartialEuler.lean#L34-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartialEuler.lean#L34-L39

import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPartialEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryTransform
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryPartialEuler.coordinate_kernel_euler {N : ℕ} (S : Finset (Fin N)) (R A : TritWord N)
    (i : Fin N) (hi : i∈S) :
    (R i).val*kernel S (predecessor R i) A=
      ((R i).val-(A i).val : ℤ)*kernel S R A := by sorry

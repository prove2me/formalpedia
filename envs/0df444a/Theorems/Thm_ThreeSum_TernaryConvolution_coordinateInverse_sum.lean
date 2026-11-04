-- Prove2me | Theorems.Thm_ThreeSum_TernaryConvolution_coordinateInverse_sum
-- name    : ThreeSum.TernaryConvolution.coordinateInverse_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:00.892198+00:00
-- url     : https://prove2.me/theorems/05195be5-3731-4433-b022-13ba656af3c9
-- title:
--   Ternary Convolution: coordinate Inverse sum
-- statement:
--   The Ternary Convolution construction uses the coordinate Inverse sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L90-L97
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L90-L97

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryTransform
import Mathlib.Algebra.BigOperators.Finprod
import Definitions.Def_Submission_ThreeSum_TernaryConvolution
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryConvolution
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryConvolution.coordinateInverse_sum {N : ℕ} {α : Type*} [Fintype α]
    (i : Fin N) (H : α → TritWord N → ℤ) (Q : TritWord N) :
    coordinateInverse i (fun R => ∑ A, H A R) Q =
      ∑ A, coordinateInverse i (H A) Q := by sorry

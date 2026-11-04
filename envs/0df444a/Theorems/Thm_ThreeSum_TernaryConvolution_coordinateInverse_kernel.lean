-- Prove2me | Theorems.Thm_ThreeSum_TernaryConvolution_coordinateInverse_kernel
-- name    : ThreeSum.TernaryConvolution.coordinateInverse_kernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:02.317+00:00
-- url     : https://prove2.me/theorems/b303e6fe-3f17-477b-b568-d50b98f9892d
-- title:
--   Ternary Convolution: coordinate Inverse kernel
-- statement:
--   The Ternary Convolution construction uses the coordinate Inverse kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L99-L126
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L99-L126

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

theorem ThreeSum.TernaryConvolution.coordinateInverse_kernel {N : ℕ} (s : Finset (Fin N)) (i : Fin N)
    (hi : i∉s) (A Q : TritWord N) (C : ℤ) :
    coordinateInverse i (fun R => partialKernel s R A*C) Q =
      partialKernel (insert i s) Q A*C := by sorry

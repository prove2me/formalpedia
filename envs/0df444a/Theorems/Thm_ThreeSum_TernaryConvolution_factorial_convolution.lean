-- Prove2me | Theorems.Thm_ThreeSum_TernaryConvolution_factorial_convolution
-- name    : ThreeSum.TernaryConvolution.factorial_convolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:24.059716+00:00
-- url     : https://prove2.me/theorems/cbe60e1e-5a00-4c4d-86e3-64a9780415ad
-- title:
--   Ternary Convolution: factorial convolution
-- statement:
--   The top-rank coefficient is exactly the original convolution, times Q!.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L261-L286
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L261-L286

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

theorem ThreeSum.TernaryConvolution.factorial_convolution {N a b : ℕ} (f g : TritWord N → ℤ)
    (hf : ∀ A, f A≠0 → rank A=a) (hg : ∀ B, g B≠0 → rank B=b)
    (Q : TritWord N) (hQ : rank Q=a+b) :
    binomialInverse
      (fun R => binomialZeta (fun A => factorial A*f A) R *
        binomialZeta (fun B => factorial B*g B) R) Q =
      factorial Q * convolution f g Q := by sorry

-- Prove2me | Theorems.Thm_ThreeSum_TernaryConvolution_stages_factorial_convolution
-- name    : ThreeSum.TernaryConvolution.stages_factorial_convolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:15.295273+00:00
-- url     : https://prove2.me/theorems/57fcf083-8941-4089-a1c8-f0e6482d92b5
-- title:
--   Ternary Convolution: stages factorial convolution
-- statement:
--   The actual coordinate transforms have the exact top-rank convolution law.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L289-L300
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L289-L300

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

theorem ThreeSum.TernaryConvolution.stages_factorial_convolution {N a b : ℕ} (coords : List (Fin N))
    (hn : coords.Nodup) (hall : coords.toFinset=univ) (f g : TritWord N → ℤ)
    (hf : ∀ A, f A≠0 → rank A=a) (hg : ∀ B, g B≠0 → rank B=b)
    (Q : TritWord N) (hQ : rank Q=a+b) :
    runInverse coords
      (fun R => runZeta coords (fun A => factorial A*f A) R *
        runZeta coords (fun B => factorial B*g B) R) Q =
      factorial Q * convolution f g Q := by sorry

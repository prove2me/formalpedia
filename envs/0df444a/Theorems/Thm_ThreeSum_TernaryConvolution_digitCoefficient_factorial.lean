-- Prove2me | Theorems.Thm_ThreeSum_TernaryConvolution_digitCoefficient_factorial
-- name    : ThreeSum.TernaryConvolution.digitCoefficient_factorial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:16.532455+00:00
-- url     : https://prove2.me/theorems/aa2c86fc-08f5-4629-84fb-153f929f22b0
-- title:
--   Ternary Convolution: digit Coefficient factorial
-- statement:
--   The Ternary Convolution construction uses the digit Coefficient factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L187-L192
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L187-L192

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

theorem ThreeSum.TernaryConvolution.digitCoefficient_factorial (q a b : Fin 3) (h : a.val+b.val=q.val) :
    digitCoefficient q a b * (a.val.factorial : ℤ) * (b.val.factorial : ℤ) =
      (q.val.factorial : ℤ) := by sorry

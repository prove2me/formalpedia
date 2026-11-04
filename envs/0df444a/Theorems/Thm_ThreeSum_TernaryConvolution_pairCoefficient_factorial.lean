-- Prove2me | Theorems.Thm_ThreeSum_TernaryConvolution_pairCoefficient_factorial
-- name    : ThreeSum.TernaryConvolution.pairCoefficient_factorial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:16.114202+00:00
-- url     : https://prove2.me/theorems/f93ce96f-6d61-4ef3-b36d-4fb59bb45f0d
-- title:
--   Ternary Convolution: pair Coefficient factorial
-- statement:
--   The Ternary Convolution construction uses the pair Coefficient factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L213-L227
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L213-L227

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

theorem ThreeSum.TernaryConvolution.pairCoefficient_factorial {N : ℕ} (Q A B : TritWord N)
    (hrank : rank A+rank B=rank Q) :
    pairCoefficient Q A B * factorial A * factorial B =
      if Adds A B Q then factorial Q else 0 := by sorry

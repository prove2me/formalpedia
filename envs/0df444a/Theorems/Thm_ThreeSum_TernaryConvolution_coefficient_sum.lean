-- Prove2me | Theorems.Thm_ThreeSum_TernaryConvolution_coefficient_sum
-- name    : ThreeSum.TernaryConvolution.coefficient_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:19.826368+00:00
-- url     : https://prove2.me/theorems/675143d3-0b2f-4574-b295-24f8d14f8c88
-- title:
--   Ternary Convolution: coefficient sum
-- statement:
--   The Ternary Convolution construction uses the coefficient sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L229-L237
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L229-L237

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

theorem ThreeSum.TernaryConvolution.coefficient_sum {N : ℕ} (Q A B : TritWord N) :
    (∑ R : TritWord N, inverseWeight Q R * weight R A * weight R B) =
      pairCoefficient Q A B := by sorry

-- Prove2me | Theorems.Thm_ThreeSum_TernaryConvolution_inverse_product_expand
-- name    : ThreeSum.TernaryConvolution.inverse_product_expand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:13.783324+00:00
-- url     : https://prove2.me/theorems/d7a9f7a4-8f60-474c-a310-6f35c3618563
-- title:
--   Ternary Convolution: inverse product expand
-- statement:
--   The Ternary Convolution construction uses the inverse product expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L239-L258
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L239-L258

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

theorem ThreeSum.TernaryConvolution.inverse_product_expand {N : ℕ} (f g : TritWord N → ℤ) (Q : TritWord N) :
    binomialInverse (fun R => binomialZeta f R * binomialZeta g R) Q =
      ∑ A, ∑ B, pairCoefficient Q A B * f A * g B := by sorry

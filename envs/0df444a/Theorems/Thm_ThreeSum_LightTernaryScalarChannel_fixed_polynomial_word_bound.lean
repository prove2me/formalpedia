-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryScalarChannel_fixed_polynomial_word_bound
-- name    : ThreeSum.LightTernaryScalarChannel.fixed_polynomial_word_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:56:46.681092+00:00
-- url     : https://prove2.me/theorems/fc57e953-d4b0-43b7-9fa0-175297f57524
-- title:
--   Light Ternary Scalar Channel: fixed polynomial word bound
-- statement:
--   The Light Ternary Scalar Channel construction uses the fixed polynomial word bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryScalarChannel.lean#L51-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryScalarChannel.lean#L51-L64

import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryScalarChannel
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryScalarChannel
open Light LightFixedArithmetic TernaryWeightChannels
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightTernaryScalarChannel.fixed_polynomial_word_bound (e : Circuit) (U : ℕ) :
    max (U : ℤ) (e.bound U)≤(e.coefficient+1)*((U : ℤ)+1)^(e.degree+1) := by sorry

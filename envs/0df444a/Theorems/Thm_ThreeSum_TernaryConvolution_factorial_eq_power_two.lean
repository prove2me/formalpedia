-- Prove2me | Theorems.Thm_ThreeSum_TernaryConvolution_factorial_eq_power_two
-- name    : ThreeSum.TernaryConvolution.factorial_eq_power_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:20:59.930889+00:00
-- url     : https://prove2.me/theorems/54ae551b-2872-47d2-9e63-0818092f04c4
-- title:
--   Ternary Convolution: factorial eq power two
-- statement:
--   The Ternary Convolution construction uses the factorial eq power two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L38-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L38-L46

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

theorem ThreeSum.TernaryConvolution.factorial_eq_power_two {N : ℕ} (A : TritWord N) :
    factorial A=(2 : ℤ)^digitCount A 2 := by sorry

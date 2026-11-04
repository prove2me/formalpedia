-- Prove2me | Theorems.Thm_ThreeSum_TernaryConvolution_runInverse_eq_binomialInverse
-- name    : ThreeSum.TernaryConvolution.runInverse_eq_binomialInverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:16.67046+00:00
-- url     : https://prove2.me/theorems/96db8700-2dbb-4817-b7c8-0f8bdf9879b6
-- title:
--   Ternary Convolution: run Inverse eq binomial Inverse
-- statement:
--   The Ternary Convolution construction uses the run Inverse eq binomial Inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L169-L174
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L169-L174

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

theorem ThreeSum.TernaryConvolution.runInverse_eq_binomialInverse {N : ℕ} (coords : List (Fin N))
    (h : coords.Nodup) (hall : coords.toFinset=univ) (H : TritWord N → ℤ) :
    runInverse coords H=binomialInverse H := by sorry

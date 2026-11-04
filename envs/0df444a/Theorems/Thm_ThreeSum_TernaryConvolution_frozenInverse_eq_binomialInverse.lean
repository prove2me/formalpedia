-- Prove2me | Theorems.Thm_ThreeSum_TernaryConvolution_frozenInverse_eq_binomialInverse
-- name    : ThreeSum.TernaryConvolution.frozenInverse_eq_binomialInverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:08.193512+00:00
-- url     : https://prove2.me/theorems/d5a94bd2-ec89-45dd-b383-4742ad884a4d
-- title:
--   Ternary Convolution: frozen Inverse eq binomial Inverse
-- statement:
--   The Ternary Convolution construction uses the frozen Inverse eq binomial Inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L148-L151
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L148-L151

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

theorem ThreeSum.TernaryConvolution.frozenInverse_eq_binomialInverse {N : ℕ} (coords : List (Fin N))
    (h : coords.Nodup) (hall : coords.toFinset=univ) (H : TritWord N → ℤ) :
    frozenInverse coords H=binomialInverse H := by sorry

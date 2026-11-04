-- Prove2me | Theorems.Thm_ThreeSum_TernaryConvolution_partialInverse_univ
-- name    : ThreeSum.TernaryConvolution.partialInverse_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:05.197113+00:00
-- url     : https://prove2.me/theorems/6ce773d1-9ff2-4465-8061-94b11f8c63e0
-- title:
--   Ternary Convolution: partial Inverse univ
-- statement:
--   The Ternary Convolution construction uses the partial Inverse univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L79-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L79-L82

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

theorem ThreeSum.TernaryConvolution.partialInverse_univ {N : ℕ} (H : TritWord N → ℤ) :
    partialInverse univ H=binomialInverse H := by sorry

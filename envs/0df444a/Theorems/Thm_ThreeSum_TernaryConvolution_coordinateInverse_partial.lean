-- Prove2me | Theorems.Thm_ThreeSum_TernaryConvolution_coordinateInverse_partial
-- name    : ThreeSum.TernaryConvolution.coordinateInverse_partial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:01.291643+00:00
-- url     : https://prove2.me/theorems/966065a2-81be-47cd-8cd7-8d10b117aaec
-- title:
--   Ternary Convolution: coordinate Inverse partial
-- statement:
--   The Ternary Convolution construction uses the coordinate Inverse partial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L128-L136
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L128-L136

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

theorem ThreeSum.TernaryConvolution.coordinateInverse_partial {N : ℕ} (s : Finset (Fin N)) (i : Fin N)
    (hi : i∉s) (H : TritWord N → ℤ) :
    coordinateInverse i (partialInverse s H)=partialInverse (insert i s) H := by sorry

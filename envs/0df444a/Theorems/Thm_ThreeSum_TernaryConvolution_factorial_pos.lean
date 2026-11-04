-- Prove2me | Theorems.Thm_ThreeSum_TernaryConvolution_factorial_pos
-- name    : ThreeSum.TernaryConvolution.factorial_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:20:58.125129+00:00
-- url     : https://prove2.me/theorems/5f2de37c-67bf-4ae2-af41-71c84697ed1c
-- title:
--   Ternary Convolution: factorial pos
-- statement:
--   The Ternary Convolution construction uses the factorial pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L48-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L48-L50

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

theorem ThreeSum.TernaryConvolution.factorial_pos {N : ℕ} (A : TritWord N) : 0<factorial A := by sorry

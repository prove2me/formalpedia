-- Prove2me | Theorems.Thm_ThreeSum_TernaryConvolution_partialInverse_empty
-- name    : ThreeSum.TernaryConvolution.partialInverse_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:04.521873+00:00
-- url     : https://prove2.me/theorems/dfc48360-c662-4152-a92d-63a58883b17a
-- title:
--   Ternary Convolution: partial Inverse empty
-- statement:
--   The Ternary Convolution construction uses the partial Inverse empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L74-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L74-L77

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

theorem ThreeSum.TernaryConvolution.partialInverse_empty {N : ℕ} (H : TritWord N → ℤ) :
    partialInverse ∅ H=H := by sorry

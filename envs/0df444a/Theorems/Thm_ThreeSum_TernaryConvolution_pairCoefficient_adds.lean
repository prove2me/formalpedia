-- Prove2me | Theorems.Thm_ThreeSum_TernaryConvolution_pairCoefficient_adds
-- name    : ThreeSum.TernaryConvolution.pairCoefficient_adds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:15.455616+00:00
-- url     : https://prove2.me/theorems/71727901-330d-44df-a86d-b60f0af9f61e
-- title:
--   Ternary Convolution: pair Coefficient adds
-- statement:
--   The Ternary Convolution construction uses the pair Coefficient adds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L194-L211
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L194-L211

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

theorem ThreeSum.TernaryConvolution.pairCoefficient_adds {N : ℕ} (Q A B : TritWord N)
    (hrank : rank A+rank B=rank Q) (hn : pairCoefficient Q A B≠0) : Adds A B Q := by sorry

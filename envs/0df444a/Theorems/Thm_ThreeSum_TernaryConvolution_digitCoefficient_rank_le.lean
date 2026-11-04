-- Prove2me | Theorems.Thm_ThreeSum_TernaryConvolution_digitCoefficient_rank_le
-- name    : ThreeSum.TernaryConvolution.digitCoefficient_rank_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:11.227053+00:00
-- url     : https://prove2.me/theorems/a5269997-7558-4e1c-a2a7-f19799fbab39
-- title:
--   Ternary Convolution: digit Coefficient rank le
-- statement:
--   The Ternary Convolution construction uses the digit Coefficient rank le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L182-L185
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L182-L185

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

theorem ThreeSum.TernaryConvolution.digitCoefficient_rank_le (q a b : Fin 3) (h : digitCoefficient q a b≠0) :
    q.val≤a.val+b.val := by sorry

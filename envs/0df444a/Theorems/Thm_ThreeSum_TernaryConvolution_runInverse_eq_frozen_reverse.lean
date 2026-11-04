-- Prove2me | Theorems.Thm_ThreeSum_TernaryConvolution_runInverse_eq_frozen_reverse
-- name    : ThreeSum.TernaryConvolution.runInverse_eq_frozen_reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:13.339719+00:00
-- url     : https://prove2.me/theorems/6dcff4e1-ba05-46d1-bbf9-fee9a334e35c
-- title:
--   Ternary Convolution: run Inverse eq frozen reverse
-- statement:
--   The Ternary Convolution construction uses the run Inverse eq frozen reverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L161-L167
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L161-L167

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

theorem ThreeSum.TernaryConvolution.runInverse_eq_frozen_reverse {N : ℕ} (coords : List (Fin N))
    (H : TritWord N → ℤ) : runInverse coords H=frozenInverse coords.reverse H := by sorry

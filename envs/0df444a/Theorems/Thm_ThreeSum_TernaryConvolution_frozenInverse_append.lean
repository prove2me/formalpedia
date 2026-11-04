-- Prove2me | Theorems.Thm_ThreeSum_TernaryConvolution_frozenInverse_append
-- name    : ThreeSum.TernaryConvolution.frozenInverse_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:04.15092+00:00
-- url     : https://prove2.me/theorems/7ebd272e-4fcb-4d14-8c79-e85dd328de3e
-- title:
--   Ternary Convolution: frozen Inverse append
-- statement:
--   The Ternary Convolution construction uses the frozen Inverse append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L153-L159
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L153-L159

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

theorem ThreeSum.TernaryConvolution.frozenInverse_append {N : ℕ} (xs ys : List (Fin N)) (H : TritWord N → ℤ) :
    frozenInverse (xs++ys) H=frozenInverse xs (frozenInverse ys H) := by sorry

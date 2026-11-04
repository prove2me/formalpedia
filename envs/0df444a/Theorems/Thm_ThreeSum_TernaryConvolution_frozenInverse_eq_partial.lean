-- Prove2me | Theorems.Thm_ThreeSum_TernaryConvolution_frozenInverse_eq_partial
-- name    : ThreeSum.TernaryConvolution.frozenInverse_eq_partial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:21:11.120122+00:00
-- url     : https://prove2.me/theorems/c2d656b4-f9b5-4041-8704-cc8a5536e370
-- title:
--   Ternary Convolution: frozen Inverse eq partial
-- statement:
--   The Ternary Convolution construction uses the frozen Inverse eq partial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L138-L146
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryConvolution.lean#L138-L146

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

theorem ThreeSum.TernaryConvolution.frozenInverse_eq_partial {N : ℕ} (coords : List (Fin N)) (h : coords.Nodup)
    (H : TritWord N → ℤ) : frozenInverse coords H=partialInverse coords.toFinset H := by sorry

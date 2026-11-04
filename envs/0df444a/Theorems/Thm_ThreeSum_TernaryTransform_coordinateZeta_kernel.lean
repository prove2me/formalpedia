-- Prove2me | Theorems.Thm_ThreeSum_TernaryTransform_coordinateZeta_kernel
-- name    : ThreeSum.TernaryTransform.coordinateZeta_kernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:18:19.565976+00:00
-- url     : https://prove2.me/theorems/9e588f4c-15af-4e28-b6d0-885e16f5f125
-- title:
--   Ternary Transform: coordinate Zeta kernel
-- statement:
--   The Ternary Transform construction uses the coordinate Zeta kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTransform.lean#L52-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTransform.lean#L52-L78

import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_ThreeSum_TernaryTransform
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTransform
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryQuery ThreeSum.TernaryEuler

theorem ThreeSum.TernaryTransform.coordinateZeta_kernel {N : ℕ} (s : Finset (Fin N)) (i : Fin N)
    (hi : i ∉ s) (A R : TritWord N) (C : ℤ) :
    coordinateZeta i (fun Q => kernel s Q A * C) R = kernel (insert i s) R A * C := by sorry

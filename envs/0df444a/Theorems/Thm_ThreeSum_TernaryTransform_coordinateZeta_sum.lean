-- Prove2me | Theorems.Thm_ThreeSum_TernaryTransform_coordinateZeta_sum
-- name    : ThreeSum.TernaryTransform.coordinateZeta_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:18:16.983202+00:00
-- url     : https://prove2.me/theorems/61f9abf4-c70e-49f6-a36c-00f98eca0144
-- title:
--   Ternary Transform: coordinate Zeta sum
-- statement:
--   The Ternary Transform construction uses the coordinate Zeta sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTransform.lean#L44-L50
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTransform.lean#L44-L50

import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_ThreeSum_TernaryTransform
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTransform
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryQuery ThreeSum.TernaryEuler

theorem ThreeSum.TernaryTransform.coordinateZeta_sum {N : ℕ} {α : Type*} [Fintype α]
    (i : Fin N) (H : α → TritWord N → ℤ) (R : TritWord N) :
    coordinateZeta i (fun Q => ∑ A, H A Q) R = ∑ A, coordinateZeta i (H A) R := by sorry

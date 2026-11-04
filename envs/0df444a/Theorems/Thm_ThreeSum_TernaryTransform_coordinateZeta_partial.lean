-- Prove2me | Theorems.Thm_ThreeSum_TernaryTransform_coordinateZeta_partial
-- name    : ThreeSum.TernaryTransform.coordinateZeta_partial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:18:14.992608+00:00
-- url     : https://prove2.me/theorems/8e32d983-a3f9-411c-9ddc-7bae2b35049d
-- title:
--   Ternary Transform: coordinate Zeta partial
-- statement:
--   The Ternary Transform construction uses the coordinate Zeta partial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTransform.lean#L80-L88
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTransform.lean#L80-L88

import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_ThreeSum_TernaryTransform
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTransform
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryQuery ThreeSum.TernaryEuler

theorem ThreeSum.TernaryTransform.coordinateZeta_partial {N : ℕ} (s : Finset (Fin N)) (i : Fin N)
    (hi : i ∉ s) (f : TritWord N → ℤ) :
    coordinateZeta i (stageSum s f) = stageSum (insert i s) f := by sorry

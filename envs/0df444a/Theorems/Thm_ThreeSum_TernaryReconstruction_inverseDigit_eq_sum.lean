-- Prove2me | Theorems.Thm_ThreeSum_TernaryReconstruction_inverseDigit_eq_sum
-- name    : ThreeSum.TernaryReconstruction.inverseDigit_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:01:57.109306+00:00
-- url     : https://prove2.me/theorems/5de8697d-614e-4d79-a8c7-86b4d8ec0b37
-- title:
--   Ternary Reconstruction: inverse Digit eq sum
-- statement:
--   The Ternary Reconstruction construction uses the inverse Digit eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryReconstruction.lean#L91-L96
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryReconstruction.lean#L91-L96

import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryReconstruction
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryQuery ThreeSum.TernaryEuler

theorem ThreeSum.TernaryReconstruction.inverseDigit_eq_sum (f : Fin 3 → ℤ) (q : Fin 3) :
    inverseDigit f q = ∑ r : Fin 3, inverseCoefficient q r * f r := by sorry

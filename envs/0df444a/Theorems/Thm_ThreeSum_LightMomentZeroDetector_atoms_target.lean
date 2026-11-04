-- Prove2me | Theorems.Thm_ThreeSum_LightMomentZeroDetector_atoms_target
-- name    : ThreeSum.LightMomentZeroDetector.atoms_target
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:43:03.524195+00:00
-- url     : https://prove2.me/theorems/862eccbb-a73d-4ce9-838c-58c108242ac6
-- title:
--   Light Moment Zero Detector: atoms target
-- statement:
--   The Light Moment Zero Detector construction uses the atoms target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentZeroDetector.lean#L13-L14
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentZeroDetector.lean#L13-L14

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_LightMomentZeroDetector
set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentZeroDetector
open Light ThreeSum.LightMomentDeterminant ThreeSum.LightFixedArithmetic
open FiniteMomentZeroDetector

theorem ThreeSum.LightMomentZeroDetector.atoms_target (H base : ℕ) (a : ℤ) (μ : ℕ → ℤ) :
    (atoms H 0).val ⟨frame [base,a],μ⟩=a := by sorry

attribute [defeq] ThreeSum.LightMomentZeroDetector.atoms_target

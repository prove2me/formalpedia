-- Prove2me | Theorems.Thm_ThreeSum_LightMomentZeroDetector_atoms_moment
-- name    : ThreeSum.LightMomentZeroDetector.atoms_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:52:59.253289+00:00
-- url     : https://prove2.me/theorems/ca248a73-7f70-438b-8722-bebf4f4228a7
-- title:
--   Light Moment Zero Detector: atoms moment
-- statement:
--   The Light Moment Zero Detector construction uses the atoms moment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentZeroDetector.lean#L16-L18
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentZeroDetector.lean#L16-L18

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_LightMomentZeroDetector
set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentZeroDetector
open Light ThreeSum.LightMomentDeterminant ThreeSum.LightFixedArithmetic
open FiniteMomentZeroDetector

theorem ThreeSum.LightMomentZeroDetector.atoms_moment (H base k : ℕ) (a : ℤ) (μ : ℕ → ℤ) (hk : k≤2*H) :
    (atoms H (k+1)).val ⟨frame [base,a],μ⟩=μ (base+k) := by sorry

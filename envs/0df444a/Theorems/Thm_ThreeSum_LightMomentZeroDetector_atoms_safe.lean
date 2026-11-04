-- Prove2me | Theorems.Thm_ThreeSum_LightMomentZeroDetector_atoms_safe
-- name    : ThreeSum.LightMomentZeroDetector.atoms_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:22:37.674015+00:00
-- url     : https://prove2.me/theorems/2ea29fd6-1321-48d1-97a3-ffdd30f024f2
-- title:
--   Light Moment Zero Detector: atoms safe
-- statement:
--   The Light Moment Zero Detector construction uses the atoms safe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentZeroDetector.lean#L20-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentZeroDetector.lean#L20-L36

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_LightMomentZeroDetector
set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentZeroDetector
open Light ThreeSum.LightMomentDeterminant ThreeSum.LightFixedArithmetic
open FiniteMomentZeroDetector

theorem ThreeSum.LightMomentZeroDetector.atoms_safe (H base : ℕ) (a : ℤ) (μ : ℕ → ℤ) {lim : Limits}
    (hspace : base+(2*H+1)≤lim.space) (hw : (lim.space : ℤ)≤lim.word) :
    ∀ i, (atoms H i).Safe lim ⟨frame [base,a],μ⟩ := by sorry

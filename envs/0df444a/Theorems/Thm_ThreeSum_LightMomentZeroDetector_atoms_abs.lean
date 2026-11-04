-- Prove2me | Theorems.Thm_ThreeSum_LightMomentZeroDetector_atoms_abs
-- name    : ThreeSum.LightMomentZeroDetector.atoms_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:22:44.878525+00:00
-- url     : https://prove2.me/theorems/cd54ddc7-3136-469a-acf4-11f5f52d6d8d
-- title:
--   Light Moment Zero Detector: atoms abs
-- statement:
--   The Light Moment Zero Detector construction uses the atoms abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentZeroDetector.lean#L38-L48
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentZeroDetector.lean#L38-L48

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_LightMomentZeroDetector
set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentZeroDetector
open Light ThreeSum.LightMomentDeterminant ThreeSum.LightFixedArithmetic
open FiniteMomentZeroDetector

theorem ThreeSum.LightMomentZeroDetector.atoms_abs (H base : ℕ) (a : ℤ) (μ : ℕ → ℤ) (U : ℤ)
    (hU : 0≤U) (ha : |a|≤U) (hm : ∀ k≤2*H, |μ (base+k)|≤U) :
    ∀ i, |(atoms H i).val ⟨frame [base,a],μ⟩|≤U := by sorry

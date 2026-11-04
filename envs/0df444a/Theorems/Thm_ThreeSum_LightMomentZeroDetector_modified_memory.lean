-- Prove2me | Theorems.Thm_ThreeSum_LightMomentZeroDetector_modified_memory
-- name    : ThreeSum.LightMomentZeroDetector.modified_memory
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:23:08.537215+00:00
-- url     : https://prove2.me/theorems/1ded9e3c-a775-45b6-8528-0b83eed1c11e
-- title:
--   Light Moment Zero Detector: modified memory
-- statement:
--   The Light Moment Zero Detector construction uses the modified memory property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentZeroDetector.lean#L61-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentZeroDetector.lean#L61-L77

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_LightMomentZeroDetector
set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentZeroDetector
open Light ThreeSum.LightMomentDeterminant ThreeSum.LightFixedArithmetic
open FiniteMomentZeroDetector

theorem ThreeSum.LightMomentZeroDetector.modified_memory (H base : ℕ) (a : ℤ) (μ : ℕ → ℤ) {t : ℕ}
    (v w : Fin t → ℤ) (hm : ∀ k≤2*H, μ (base+k)=moment v w k)
    (d : ℕ) (hd : d≤H) :
    (modified d).eval (fun i => (atoms H i).val ⟨frame [base,a],μ⟩)=(modifiedHankel v w a d).det := by sorry

-- Prove2me | Theorems.Thm_ThreeSum_LightMomentZeroDetector_leading_memory
-- name    : ThreeSum.LightMomentZeroDetector.leading_memory
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:23:03.301464+00:00
-- url     : https://prove2.me/theorems/6f6cd122-b161-4ef9-9838-f9ddf543968f
-- title:
--   Light Moment Zero Detector: leading memory
-- statement:
--   The Light Moment Zero Detector construction uses the leading memory property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentZeroDetector.lean#L50-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMomentZeroDetector.lean#L50-L59

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_LightMomentZeroDetector
set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentZeroDetector
open Light ThreeSum.LightMomentDeterminant ThreeSum.LightFixedArithmetic
open FiniteMomentZeroDetector

theorem ThreeSum.LightMomentZeroDetector.leading_memory (H base : ℕ) (a : ℤ) (μ : ℕ → ℤ) {t : ℕ}
    (v w : Fin t → ℤ) (hm : ∀ k≤2*H, μ (base+k)=moment v w k)
    (d : ℕ) (hd : d≤H) :
    (leading d).eval (fun i => (atoms H i).val ⟨frame [base,a],μ⟩)=(hankel v w d).det := by sorry

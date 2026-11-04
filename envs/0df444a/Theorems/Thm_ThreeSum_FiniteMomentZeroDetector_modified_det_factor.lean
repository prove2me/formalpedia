-- Prove2me | Theorems.Thm_ThreeSum_FiniteMomentZeroDetector_modified_det_factor
-- name    : ThreeSum.FiniteMomentZeroDetector.modified_det_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:41:33.688262+00:00
-- url     : https://prove2.me/theorems/bc6b7186-240e-472a-8e30-680859227904
-- title:
--   Finite Moment Zero Detector: modified det factor
-- statement:
--   The Finite Moment Zero Detector construction uses the modified det factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/FiniteMomentZeroDetector.lean#L101-L104
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/FiniteMomentZeroDetector.lean#L101-L104

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
set_option autoImplicit false
open ThreeSum ThreeSum.FiniteMomentZeroDetector
open Matrix Finset
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem ThreeSum.FiniteMomentZeroDetector.modified_det_factor {t : ℕ} (v w : Fin t → ℤ) (a : ℤ) :
    (modifiedHankel v w a t).det=(hankel v w t).det * ∏ s, (v s-a)^2 := by sorry

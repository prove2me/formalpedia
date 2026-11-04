-- Prove2me | Theorems.Thm_ThreeSum_FiniteMomentZeroDetector_det_hankel_eq_zero_of_support_lt
-- name    : ThreeSum.FiniteMomentZeroDetector.det_hankel_eq_zero_of_support_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:41:29.564077+00:00
-- url     : https://prove2.me/theorems/c58a6194-9e0a-4cb2-b5c5-ae8db876e007
-- title:
--   Finite Moment Zero Detector: det hankel eq zero of support lt
-- statement:
--   The Finite Moment Zero Detector construction uses the det hankel eq zero of support lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/FiniteMomentZeroDetector.lean#L55-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/FiniteMomentZeroDetector.lean#L55-L64

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
set_option autoImplicit false
open ThreeSum ThreeSum.FiniteMomentZeroDetector
open Matrix Finset
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem ThreeSum.FiniteMomentZeroDetector.det_hankel_eq_zero_of_support_lt {t d : ℕ} (v w : Fin t → ℤ) (ht : t<d) :
    (hankel v w d).det=0 := by sorry

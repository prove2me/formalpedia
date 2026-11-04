-- Prove2me | Theorems.Thm_ThreeSum_FiniteMomentZeroDetector_modified_det_zero_iff
-- name    : ThreeSum.FiniteMomentZeroDetector.modified_det_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:41:35.711387+00:00
-- url     : https://prove2.me/theorems/7b66aee5-6d4e-43d1-a4b9-e932af2041bc
-- title:
--   Finite Moment Zero Detector: modified det zero iff
-- statement:
--   The Finite Moment Zero Detector construction uses the modified det zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/FiniteMomentZeroDetector.lean#L106-L112
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/FiniteMomentZeroDetector.lean#L106-L112

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
set_option autoImplicit false
open ThreeSum ThreeSum.FiniteMomentZeroDetector
open Matrix Finset
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem ThreeSum.FiniteMomentZeroDetector.modified_det_zero_iff {t : ℕ} (v w : Fin t → ℤ) (a : ℤ)
    (hv : Function.Injective v) (hw : ∀ s, w s≠0) :
    (modifiedHankel v w a t).det=0 ↔ ∃ s, v s=a := by sorry

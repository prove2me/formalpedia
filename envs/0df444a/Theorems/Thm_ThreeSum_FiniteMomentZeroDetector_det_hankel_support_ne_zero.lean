-- Prove2me | Theorems.Thm_ThreeSum_FiniteMomentZeroDetector_det_hankel_support_ne_zero
-- name    : ThreeSum.FiniteMomentZeroDetector.det_hankel_support_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:41:31.153538+00:00
-- url     : https://prove2.me/theorems/ef646c67-2e4f-4917-9ffa-ea5ff95d395b
-- title:
--   Finite Moment Zero Detector: det hankel support ne zero
-- statement:
--   The Finite Moment Zero Detector construction uses the det hankel support ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/FiniteMomentZeroDetector.lean#L48-L53
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/FiniteMomentZeroDetector.lean#L48-L53

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
set_option autoImplicit false
open ThreeSum ThreeSum.FiniteMomentZeroDetector
open Matrix Finset
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem ThreeSum.FiniteMomentZeroDetector.det_hankel_support_ne_zero {t : ℕ} (v w : Fin t → ℤ)
    (hv : Function.Injective v) (hw : ∀ s, w s≠0) :
    (hankel v w t).det≠0 := by sorry

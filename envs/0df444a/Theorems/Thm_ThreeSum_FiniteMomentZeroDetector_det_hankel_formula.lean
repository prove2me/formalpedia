-- Prove2me | Theorems.Thm_ThreeSum_FiniteMomentZeroDetector_det_hankel_formula
-- name    : ThreeSum.FiniteMomentZeroDetector.det_hankel_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:41:28.04718+00:00
-- url     : https://prove2.me/theorems/9c8b88b6-3f58-42c4-b6c0-4654ea178885
-- title:
--   Finite Moment Zero Detector: det hankel formula
-- statement:
--   The Finite Moment Zero Detector construction uses the det hankel formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/FiniteMomentZeroDetector.lean#L42-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/FiniteMomentZeroDetector.lean#L42-L46

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
set_option autoImplicit false
open ThreeSum ThreeSum.FiniteMomentZeroDetector
open Matrix Finset
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem ThreeSum.FiniteMomentZeroDetector.det_hankel_formula {t : ℕ} (v w : Fin t → ℤ) :
    (hankel v w t).det=(vandermonde v).det^2 * ∏ s, w s := by sorry

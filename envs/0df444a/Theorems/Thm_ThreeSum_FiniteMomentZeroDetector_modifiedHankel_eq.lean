-- Prove2me | Theorems.Thm_ThreeSum_FiniteMomentZeroDetector_modifiedHankel_eq
-- name    : ThreeSum.FiniteMomentZeroDetector.modifiedHankel_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:41:31.633207+00:00
-- url     : https://prove2.me/theorems/470ec77d-8a43-4d2c-a2ca-eab9f0105cf4
-- title:
--   Finite Moment Zero Detector: modified Hankel eq
-- statement:
--   The Finite Moment Zero Detector construction uses the modified Hankel eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/FiniteMomentZeroDetector.lean#L96-L99
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/FiniteMomentZeroDetector.lean#L96-L99

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
set_option autoImplicit false
open ThreeSum ThreeSum.FiniteMomentZeroDetector
open Matrix Finset
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem ThreeSum.FiniteMomentZeroDetector.modifiedHankel_eq {t : ℕ} (v w : Fin t → ℤ) (a : ℤ) (d : ℕ) :
    modifiedHankel v w a d=hankel v (fun s => w s*(v s-a)^2) d := by sorry

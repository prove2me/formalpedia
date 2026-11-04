-- Prove2me | Theorems.Thm_ThreeSum_FiniteMomentZeroDetector_modifiedMoment_eq
-- name    : ThreeSum.FiniteMomentZeroDetector.modifiedMoment_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:41:31.728783+00:00
-- url     : https://prove2.me/theorems/79fb7595-f9c6-4ade-a257-bcb30fffa4a6
-- title:
--   Finite Moment Zero Detector: modified Moment eq
-- statement:
--   The Finite Moment Zero Detector construction uses the modified Moment eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/FiniteMomentZeroDetector.lean#L83-L91
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/FiniteMomentZeroDetector.lean#L83-L91

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
set_option autoImplicit false
open ThreeSum ThreeSum.FiniteMomentZeroDetector
open Matrix Finset
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem ThreeSum.FiniteMomentZeroDetector.modifiedMoment_eq {t : ℕ} (v w : Fin t → ℤ) (a : ℤ) (k : ℕ) :
    modifiedMoment v w a k=moment v (fun s => w s*(v s-a)^2) k := by sorry

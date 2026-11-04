-- Prove2me | Theorems.Thm_ThreeSum_FiniteMomentZeroDetector_hankel_factor
-- name    : ThreeSum.FiniteMomentZeroDetector.hankel_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:41:28.896019+00:00
-- url     : https://prove2.me/theorems/4ae0fb86-077a-4a51-ba6d-39f4b660af7d
-- title:
--   Finite Moment Zero Detector: hankel factor
-- statement:
--   The Finite Moment Zero Detector construction uses the hankel factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/FiniteMomentZeroDetector.lean#L31-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/FiniteMomentZeroDetector.lean#L31-L40

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
set_option autoImplicit false
open ThreeSum ThreeSum.FiniteMomentZeroDetector
open Matrix Finset
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem ThreeSum.FiniteMomentZeroDetector.hankel_factor {t : ℕ} (v w : Fin t → ℤ) (d : ℕ) :
    hankel v w d=(powerTable v d)ᵀ * diagonal w * powerTable v d := by sorry

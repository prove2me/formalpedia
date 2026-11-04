-- Prove2me | Theorems.Thm_ThreeSum_FiniteMomentZeroDetector_support_of_largest_nonzero
-- name    : ThreeSum.FiniteMomentZeroDetector.support_of_largest_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:41:29.589905+00:00
-- url     : https://prove2.me/theorems/fa516f76-0c40-48da-a231-affd9e2322ec
-- title:
--   Finite Moment Zero Detector: support of largest nonzero
-- statement:
--   Any largest nonzero leading determinant has the actual support size.
--   This also handles the empty measure, since the dimension-zero determinant
--   is one.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/FiniteMomentZeroDetector.lean#L69-L78
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/FiniteMomentZeroDetector.lean#L69-L78

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
set_option autoImplicit false
open ThreeSum ThreeSum.FiniteMomentZeroDetector
open Matrix Finset
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem ThreeSum.FiniteMomentZeroDetector.support_of_largest_nonzero {t h d : ℕ} (v w : Fin t → ℤ)
    (hv : Function.Injective v) (hw : ∀ s, w s≠0) (hth : t≤h)
    (_hdh : d≤h) (hd : (hankel v w d).det≠0)
    (hmax : ∀ k≤h, (hankel v w k).det≠0 → k≤d) : d=t := by sorry

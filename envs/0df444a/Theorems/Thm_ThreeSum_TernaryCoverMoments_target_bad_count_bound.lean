-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverMoments_target_bad_count_bound
-- name    : ThreeSum.TernaryCoverMoments.target_bad_count_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:56:48.55123+00:00
-- url     : https://prove2.me/theorems/86612b39-e09c-4f18-be26-bf3ecd12f150
-- title:
--   Ternary Cover Moments: target bad count bound
-- statement:
--   The Ternary Cover Moments construction uses the target bad count bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverMoments.lean#L82-L92
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverMoments.lean#L82-L92

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverMoments
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverMoments
open Finset
open scoped BigOperators
variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq Ω]
variable {T : Type*} [Fintype T] [DecidableEq T]

theorem ThreeSum.TernaryCoverMoments.target_bad_count_bound (X : Ω → T → ℕ) (k τ : ℕ) (t : T) :
    τ ^ k * (univ.filter fun w => τ < X w t).card ≤ ∑ w, X w t ^ k := by sorry

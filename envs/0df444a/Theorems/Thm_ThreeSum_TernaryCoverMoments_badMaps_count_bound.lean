-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverMoments_badMaps_count_bound
-- name    : ThreeSum.TernaryCoverMoments.badMaps_count_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:55:29.463666+00:00
-- url     : https://prove2.me/theorems/31db683e-bca2-4405-b067-feaaee5725d9
-- title:
--   Ternary Cover Moments: bad Maps count bound
-- statement:
--   All literal target pairs are included in the union bound.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverMoments.lean#L95-L113
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverMoments.lean#L95-L113

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

theorem ThreeSum.TernaryCoverMoments.badMaps_count_bound (X : Ω → T → ℕ) (k τ C : ℕ)
    (hmoment : ∀ t : T, (∑ w, X w t ^ k) ≤ C * Fintype.card Ω) :
    τ ^ k * (badMaps X τ).card ≤ Fintype.card T * C * Fintype.card Ω := by sorry

-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverMoments_removed_mass_bound
-- name    : ThreeSum.TernaryCoverMoments.removed_mass_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:55:46.74161+00:00
-- url     : https://prove2.me/theorems/1a6c7589-4267-4cf2-b9bf-de9975dcde03
-- title:
--   Ternary Cover Moments: removed mass bound
-- statement:
--   Retained target mass removed by a global raw-cap test is bounded by the
--   actual retained fiber cap.  The cap factor must be charged before choosing
--   the high moment order.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverMoments.lean#L118-L123
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverMoments.lean#L118-L123

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

theorem ThreeSum.TernaryCoverMoments.removed_mass_bound (f : Ω → ℕ) (bad : Finset Ω) (B : ℕ)
    (hcap : ∀ w, f w ≤ B ^ 2) :
    (∑ w ∈ bad, f w) ≤ B ^ 2 * bad.card := by sorry

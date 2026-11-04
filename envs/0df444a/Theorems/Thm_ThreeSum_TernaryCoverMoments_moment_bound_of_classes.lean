-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverMoments_moment_bound_of_classes
-- name    : ThreeSum.TernaryCoverMoments.moment_bound_of_classes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:56:43.138192+00:00
-- url     : https://prove2.me/theorems/9fa64300-cf15-4067-8512-42698e11ac30
-- title:
--   Ternary Cover Moments: moment bound of classes
-- statement:
--   Exact cancellation of one fixed relation class's rank exponent.
--   The class-count and hash-fiber hypotheses are exposed, rather than hidden
--   inside an assumed moment estimate.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverMoments.lean#L43-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverMoments.lean#L43-L73

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

theorem ThreeSum.TernaryCoverMoments.moment_bound_of_classes {C : Type*} [Fintype C] [DecidableEq C]
    (events : E → Finset Ω) (k p : ℕ) (hp : 0 < p)
    (classify : (Fin k → E) → C) (rank : C → ℕ)
    (hcount : ∀ c : C, (univ.filter fun es => classify es = c).card ≤ p ^ rank c)
    (hhash : ∀ es : Fin k → E,
      p ^ rank (classify es) * (jointEvent events es).card ≤ Fintype.card Ω) :
    (∑ w, HashFamily.incidenceCount events w ^ k) ≤ Fintype.card C * Fintype.card Ω := by sorry

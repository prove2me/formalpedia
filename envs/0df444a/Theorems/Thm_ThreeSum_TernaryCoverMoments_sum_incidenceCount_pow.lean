-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverMoments_sum_incidenceCount_pow
-- name    : ThreeSum.TernaryCoverMoments.sum_incidenceCount_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:56:44.828487+00:00
-- url     : https://prove2.me/theorems/b5a4e998-3a5e-4c67-aa24-6e05c1daf083
-- title:
--   Ternary Cover Moments: sum incidence Count pow
-- statement:
--   The Ternary Cover Moments construction uses the sum incidence Count pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverMoments.lean#L26-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverMoments.lean#L26-L38

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

theorem ThreeSum.TernaryCoverMoments.sum_incidenceCount_pow (events : E → Finset Ω) (k : ℕ) :
    (∑ w, HashFamily.incidenceCount events w ^ k) =
      ∑ es : Fin k → E, (jointEvent events es).card := by sorry

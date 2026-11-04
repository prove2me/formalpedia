-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_raw_second_moment_w3sum_ac885d1
-- name    : ThreeSum.HashFamily.raw_second_moment_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:51.473266+00:00
-- url     : https://prove2.me/theorems/98671903-2aa9-4dfe-97e7-86f81a34e66b
-- title:
--   Hash Family: raw second moment
-- statement:
--   Full second moment, derived by counting the exceptional partner classes.
--   `B` bounds the number of shared-endpoint or same-output partners per edge;
--   the local graph instantiation takes `B = 2*Delta + G`.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L524-L560
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L524-L560

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSum_HashFamily
set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]

theorem ThreeSum.HashFamily.raw_second_moment_w3sum_ac885d1 (left right : E → α → Bool)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hcross : ∀ e f, left e ≠ right f)
    (B : ℕ) (hB : ∀ e, (badPartners left right e).card ≤ B) (a b : K) :
    Fintype.card K ^ 4 *
        (∑ w, incidenceCount (fun e => pairEvent (left e) (right e) a b) w ^ 2) ≤
      Fintype.card (α × Bool → K) *
        (Fintype.card E * Fintype.card K ^ 2 + Fintype.card E ^ 2 +
          Fintype.card E * B * Fintype.card K) := by sorry

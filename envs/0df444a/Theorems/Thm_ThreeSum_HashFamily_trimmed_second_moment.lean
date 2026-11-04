-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_trimmed_second_moment
-- name    : ThreeSum.HashFamily.trimmed_second_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:03:03.683741+00:00
-- url     : https://prove2.me/theorems/aafdefd9-3a31-4804-8e9a-b360c3afdd8b
-- title:
--   Hash Family: trimmed second moment
-- statement:
--   The Hash Family construction uses the trimmed second moment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L768-L780
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L768-L780

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

theorem ThreeSum.HashFamily.trimmed_second_moment (left right : E → α → Bool)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hcross : ∀ e f, left e ≠ right f)
    (Bbad : ℕ) (hB : ∀ e, (badPartners left right e).card ≤ Bbad)
    (hBp : Bbad ≤ 3 * Fintype.card K) (hEp : Fintype.card E ≤ Fintype.card K ^ 2)
    (a b : K) (leftVertices rightVertices : Finset (α → Bool)) (Bbucket : ℕ) :
    Fintype.card K ^ 2 * (∑ w, incidenceCount
        (fun e => trimmedPairEvent (left e) (right e) a b leftVertices rightVertices Bbucket) w ^ 2) ≤
      5 * Fintype.card E * Fintype.card (α × Bool → K) := by sorry

-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_trimmed_first_moment
-- name    : ThreeSum.HashFamily.trimmed_first_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:03:05.718325+00:00
-- url     : https://prove2.me/theorems/d5d0232b-d09e-4b15-adbe-b82302ca389e
-- title:
--   Hash Family: trimmed first moment
-- statement:
--   The Hash Family construction uses the trimmed first moment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L751-L766
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L751-L766

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

theorem ThreeSum.HashFamily.trimmed_first_moment (left right : E → α → Bool)
    (hcross : ∀ e f, left e ≠ right f) (a b : K)
    (leftVertices rightVertices : Finset (α → Bool))
    (hL : ∀ e u, u ∈ leftVertices → u ≠ right e)
    (hR : ∀ e u, u ∈ rightVertices → u ≠ left e)
    (B : ℕ)
    (hBL : 4 * (Fintype.card K + leftVertices.card) ≤ B * Fintype.card K)
    (hBR : 4 * (Fintype.card K + rightVertices.card) ≤ B * Fintype.card K) :
    Fintype.card E * Fintype.card (α × Bool → K) ≤
      2 * Fintype.card K ^ 2 * (∑ w, incidenceCount
        (fun e => trimmedPairEvent (left e) (right e) a b leftVertices rightVertices B) w) := by sorry

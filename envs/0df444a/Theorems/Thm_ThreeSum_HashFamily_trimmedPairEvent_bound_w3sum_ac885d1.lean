-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_trimmedPairEvent_bound_w3sum_ac885d1
-- name    : ThreeSum.HashFamily.trimmedPairEvent_bound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:03:00.660299+00:00
-- url     : https://prove2.me/theorems/410ab29b-7751-4947-9379-b66952e42396
-- title:
--   Hash Family: trimmed Pair Event bound
-- statement:
--   Both separable masks retain at least half of every pair's raw mass.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L712-L742
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L712-L742

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
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]

theorem ThreeSum.HashFamily.trimmedPairEvent_bound_w3sum_ac885d1 {s t : α → Bool} (hst : s ≠ t) (a b : K)
    (leftVertices rightVertices : Finset (α → Bool))
    (hL : ∀ u ∈ leftVertices, u ≠ t) (hR : ∀ u ∈ rightVertices, u ≠ s)
    (B : ℕ)
    (hBL : 4 * (Fintype.card K + leftVertices.card) ≤ B * Fintype.card K)
    (hBR : 4 * (Fintype.card K + rightVertices.card) ≤ B * Fintype.card K) :
    Fintype.card (α × Bool → K) ≤ 2 * Fintype.card K ^ 2 *
      (trimmedPairEvent s t a b leftVertices rightVertices B).card := by sorry

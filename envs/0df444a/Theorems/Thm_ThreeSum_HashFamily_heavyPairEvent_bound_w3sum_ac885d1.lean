-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_heavyPairEvent_bound_w3sum_ac885d1
-- name    : ThreeSum.HashFamily.heavyPairEvent_bound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:58.937265+00:00
-- url     : https://prove2.me/theorems/0df4c545-044f-49e3-8cff-ce2e553c98ae
-- title:
--   Hash Family: heavy Pair Event bound
-- statement:
--   Discarding a bucket above the prescribed threshold loses at most a
--   quarter of each pair's raw representation mass, uniformly in the targets.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L679-L698
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L679-L698

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

theorem ThreeSum.HashFamily.heavyPairEvent_bound_w3sum_ac885d1 {s t : α → Bool} (hst : s ≠ t) (a b : K)
    (vertices : Finset (α → Bool)) (hcross : ∀ u ∈ vertices, u ≠ t)
    (B : ℕ) (hB : 4 * (Fintype.card K + vertices.card) ≤ B * Fintype.card K) :
    4 * Fintype.card K ^ 2 * (heavyPairEvent s t a b vertices B).card ≤
      Fintype.card (α × Bool → K) := by sorry

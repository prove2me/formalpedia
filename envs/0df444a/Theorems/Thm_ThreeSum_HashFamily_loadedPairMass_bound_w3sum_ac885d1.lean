-- Prove2me | Theorems.Thm_ThreeSum_HashFamily_loadedPairMass_bound_w3sum_ac885d1
-- name    : ThreeSum.HashFamily.loadedPairMass_bound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:02:57.635418+00:00
-- url     : https://prove2.me/theorems/52523554-3b08-43b8-adef-8c43e2c84a1e
-- title:
--   Hash Family: loaded Pair Mass bound
-- statement:
--   Conditional bucket-load bound proved from actual three-word uniformity.
--   The right endpoint must be outside the entire left vertex class.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L611-L656
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/HashFamily.lean#L611-L656

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

theorem ThreeSum.HashFamily.loadedPairMass_bound_w3sum_ac885d1 {s t : α → Bool} (hst : s ≠ t) (a b : K)
    (vertices : Finset (α → Bool)) (hcross : ∀ u ∈ vertices, u ≠ t) :
    Fintype.card K ^ 3 * loadedPairMass s t a b vertices ≤
      (Fintype.card K + vertices.card) * Fintype.card (α × Bool → K) := by sorry

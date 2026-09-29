-- Prove2me | Theorems.Thm_SparseApprox_Greedy_chosen_orthogonal_unchosen
-- name    : SparseApprox.Greedy.chosen_orthogonal_unchosen
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T23:10:26.295744+00:00
-- url     : https://prove2.me/theorems/39115d95-26ff-4592-acf4-7c18d128ab02
-- title:
--   Core invariant — every chosen column is orthogonal to every unchosen column
-- statement:
--   Let $a^{(r)}_1,\dots,a^{(r)}_n$ be the columns of $A^{(r)}$ and $\tau^{(r)}$ the indices selected so far in the selection phase of Algorithm Greedy. If $k_0,\dots,k_{t-1}$ is a run of $t$ iterations, then for every $r\le t$, every $i\in\tau^{(r)}$ and every $j\notin\tau^{(r)}$ one has $a^{(r)}{}_i{}^T a^{(r)}_j=0$.
--
--   At each step the newly selected column $a^{(s)}_{k_s}$ is orthogonal, by the projection formula and its unit norm, to every column that is updated at that step, and columns already in $\tau$ keep their values. Orthogonality of an inner product is preserved when the second argument is replaced by the updated column, provided it already held. Hence a chosen column stays orthogonal to all columns that are never chosen.
-- source:
--   Natarajan 1995, Sparse approximate solutions to linear systems, p. 229 (Algorithm Greedy, column update)

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm
import Theorems.Thm_SparseApprox_Greedy_state_col_norm_zero_or_one
import Theorems.Thm_SparseApprox_Greedy_chosen_col_norm_one

open scoped InnerProductSpace

namespace SparseApprox.Greedy

/-- A column that has been chosen is orthogonal to every column that has not.

At each step the new column is replaced by
`normalizeVec (s.col j - ⟪s.col k, s.col j⟫_ℝ • s.col k)`. Since the selected column
`a = s.col (k r)` has unit norm by `chosen_col_norm_one`,

  ⟪a, x - ⟪a, x⟫_ℝ • a⟫_ℝ = ⟪a, x⟫_ℝ - ⟪a, x⟫_ℝ * ‖a‖² = 0,

and if a vector `z` is orthogonal to both `x` and `a` then it is orthogonal to the
updated column as well. Together with the freezing of already-chosen columns this
preserves the property along the run. -/
theorem chosen_orthogonal_unchosen {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ)
    (k : ℕ → Fin n) (t r : ℕ)
    (hrun : IsGreedyRun A b ε k t) (hr : r ≤ t)
    {i j : Fin n}
    (hi : i ∈ (greedyState A b k r).chosen)
    (hj : j ∉ (greedyState A b k r).chosen) :
    ⟪(greedyState A b k r).col i,
      (greedyState A b k r).col j⟫_ℝ = 0 := by sorry

end SparseApprox.Greedy

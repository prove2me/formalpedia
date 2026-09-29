-- Prove2me | Theorems.Thm_SparseApprox_Greedy_chosen_residual_orthogonal
-- name    : SparseApprox.Greedy.chosen_residual_orthogonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T01:22:24.15985+00:00
-- url     : https://prove2.me/theorems/51c3b1fe-ca00-437b-8b4e-7c535a56dbdb
-- title:
--   Core invariant — every chosen column is orthogonal to the current residual
-- statement:
--   Let $a^{(r)}_1,\dots,a^{(r)}_n$ be the columns of $A^{(r)}$ and $b^{(r)}$ the residual, in the selection phase of Algorithm Greedy. If $k_0,\dots,k_{t-1}$ is a run of $t$ iterations, then for every $r\le t$ and every $i\in\tau^{(r)}$ one has $a^{(r)}{}_i{}^T b^{(r)}=0$.
--
--   At the step at which index $i$ is selected, the residual is updated to $b^{(s+1)}=b^{(s)}-\bigl(a^{(s)}{}_{k_s}{}^T b^{(s)}\bigr)a^{(s)}_{k_s}$ and $a^{(s)}_{k_s}$ is a unit vector, so $a^{(s)}{}_{k_s}{}^T b^{(s+1)}=0$. At every later step the same identity applies to the column selected then, and the previously selected column is already orthogonal to the old residual and to the newly selected column, hence to the updated residual as well.
-- source:
--   Natarajan 1995, Sparse approximate solutions to linear systems, p. 229 (Algorithm Greedy, residual update)

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm
import Theorems.Thm_SparseApprox_Greedy_state_col_norm_zero_or_one
import Theorems.Thm_SparseApprox_Greedy_chosen_col_norm_one
import Theorems.Thm_SparseApprox_Greedy_chosen_orthogonal_unchosen

open scoped InnerProductSpace

namespace SparseApprox.Greedy

/-- A column that has been chosen is orthogonal to the current residual.

The residual is updated by exactly the same rank-one rejection
`res - ⟪a, res⟫_ℝ • a` as the columns, and every chosen column is a unit vector, so

  ⟪a, res - ⟪a, res⟫_ℝ • a⟫_ℝ = ⟪a, res⟫_ℝ - ⟪a, res⟫_ℝ * ‖a‖² = 0.

A chosen column that is also orthogonal to the previously selected ones remains
orthogonal after the update. This is the statement that lets the chosen columns and
the residual be handled separately in the support/linear-independence argument. -/
theorem chosen_residual_orthogonal {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ)
    (k : ℕ → Fin n) (t r : ℕ)
    (hrun : IsGreedyRun A b ε k t) (hr : r ≤ t)
    {i : Fin n}
    (hi : i ∈ (greedyState A b k r).chosen) :
    ⟪(greedyState A b k r).col i,
      (greedyState A b k r).res⟫_ℝ = 0 := by sorry

end SparseApprox.Greedy

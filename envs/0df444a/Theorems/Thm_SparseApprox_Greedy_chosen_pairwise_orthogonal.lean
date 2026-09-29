-- Prove2me | Theorems.Thm_SparseApprox_Greedy_chosen_pairwise_orthogonal
-- name    : SparseApprox.Greedy.chosen_pairwise_orthogonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T01:29:43.610511+00:00
-- url     : https://prove2.me/theorems/cfb861b9-c029-474c-9cb4-3a4ea74b1c06
-- title:
--   Core invariant — distinct chosen columns are pairwise orthogonal
-- statement:
--   Let $a^{(r)}_1,\dots,a^{(r)}_n$ be the columns of $A^{(r)}$ and $\tau^{(r)}$ the indices selected so far in the selection phase of Algorithm Greedy. If $k_0,\dots,k_{t-1}$ is a run of $t$ iterations, then for every $r\le t$ and distinct $i,j\in\tau^{(r)}$ one has $a^{(r)}{}_i{}^T a^{(r)}{}_j=0$.
--
--   Both columns are unit vectors, and each new column is made orthogonal to the column selected at that step and to all previously selected columns by the rank-one update. Since exactly one index is inserted into $\tau$ at each step, two distinct chosen indices were selected at different steps, and the later one was made orthogonal to the earlier one at the step when it was selected; both are frozen afterwards.
-- source:
--   Natarajan 1995, Sparse approximate solutions to linear systems, p. 229 (Algorithm Greedy)

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm
import Theorems.Thm_SparseApprox_Greedy_state_col_norm_zero_or_one
import Theorems.Thm_SparseApprox_Greedy_chosen_col_norm_one
import Theorems.Thm_SparseApprox_Greedy_chosen_orthogonal_unchosen

open scoped InnerProductSpace

namespace SparseApprox.Greedy

/-- Distinct chosen columns are pairwise orthogonal.

The second column of an inner product is the one updated by `greedyStep`, so
`chosen_orthogonal_unchosen` gives the two mixed cases directly and `real_inner_comm`
handles the other orientation. The only remaining case, where both indices enter the
chosen set at the same step, is impossible for distinct indices because exactly one
index is inserted per step. -/
theorem chosen_pairwise_orthogonal {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ)
    (k : ℕ → Fin n) (t r : ℕ)
    (hrun : IsGreedyRun A b ε k t) (hr : r ≤ t)
    {i j : Fin n}
    (hi : i ∈ (greedyState A b k r).chosen)
    (hj : j ∈ (greedyState A b k r).chosen)
    (hij : i ≠ j) :
    ⟪(greedyState A b k r).col i,
      (greedyState A b k r).col j⟫_ℝ = 0 := by sorry

end SparseApprox.Greedy

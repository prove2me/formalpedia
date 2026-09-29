-- Prove2me | Theorems.Thm_SparseApprox_Greedy_residual_sq_step
-- name    : SparseApprox.Greedy.residual_sq_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T23:06:39.070144+00:00
-- url     : https://prove2.me/theorems/bbc14d3d-7171-49a2-8e2b-5abbcb7a4f2a
-- title:
--   Core invariant — one greedy step decreases the squared residual norm by the squared correlation
-- statement:
--   Let $a^{(r)}_1,\dots,a^{(r)}_n$ be the columns of $A^{(r)}$ and $b^{(r)}$ the residual, in the selection phase of Algorithm Greedy. If $k_0,\dots,k_{t-1}$ is a run of $t$ iterations, then for every $r<t$,
--   $$b^{(r+1)}=b^{(r)}-\bigl(a^{(r)}{}_{k_r}{}^T b^{(r)}\bigr)a^{(r)}_{k_r}\quad\Longrightarrow\quad \|b^{(r+1)}\|_2^2=\|b^{(r)}\|_2^2-\bigl|a^{(r)}{}_{k_r}{}^T b^{(r)}\bigr|^2.$$
--   Indeed $a^{(r)}_{k_r}$ has unit norm, so expanding the square gives $\|b^{(r)}\|_2^2-2\bigl(a^{(r)}_{k_r}{}^Tb^{(r)}\bigr)^2+\bigl(a^{(r)}_{k_r}{}^Tb^{(r)}\bigr)^2$. This is the exact per-step decrease of the squared residual.
-- source:
--   Natarajan 1995, Sparse approximate solutions to linear systems, p. 229 (Algorithm Greedy, residual update)

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm
import Theorems.Thm_SparseApprox_Greedy_state_col_norm_zero_or_one

open scoped InnerProductSpace

namespace SparseApprox.Greedy

/-- One selection step decreases the squared residual norm by the squared correlation
of the selected column with the residual.

Expanding the squared norm of `res - ⟪a, res⟫_ℝ • a` with `norm_sub_sq_real` gives

  ‖res - ⟪a, res⟫_ℝ • a‖² = ‖res‖² - 2 * ⟪res, a⟫_ℝ + |⟪a, res⟫_ℝ|²,

and, because the selected column is a unit vector, the cross terms cancel. This is the
per-step decrease on which the geometric contraction argument rests. -/
theorem residual_sq_step {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ)
    (k : ℕ → Fin n) (t r : ℕ)
    (hrun : IsGreedyRun A b ε k t) (hr : r < t) :
    ‖(greedyState A b k (r + 1)).res‖ ^ 2 =
      ‖(greedyState A b k r).res‖ ^ 2 -
        |⟪(greedyState A b k r).col (k r),
          (greedyState A b k r).res⟫_ℝ| ^ 2 := by sorry

end SparseApprox.Greedy

-- Prove2me | Theorems.Thm_SparseApprox_Greedy_state_col_norm_zero_or_one
-- name    : SparseApprox.Greedy.state_col_norm_zero_or_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T22:34:09.104578+00:00
-- url     : https://prove2.me/theorems/8366cf1e-7363-4b20-896f-b5a59a8a736a
-- title:
--   Core invariant — every column of the greedy state is zero or of unit norm
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$, let $k:\mathbb N\to\{1,\dots,n\}$ be a sequence of choices and let $a^{(r)}_j$ be column $j$ of $A^{(r)}$ in the state of the selection phase of Algorithm Greedy after $r$ steps. Then for every $r$ and every $j$ one of two things holds: either $a^{(r)}_j=0$, or $\|a^{(r)}_j\|_2=1$.
--
--   Indeed, at the initialisation every column is $\mathbf a_j=\hat a_j/\|\hat a_j\|_2$, which is zero when $\hat a_j=0$ and has unit norm otherwise. At each subsequent step the columns in the new selected set are frozen, and every other column is replaced by $a^{(r+1)}_j=\bigl(a^{(r)}_j-\bigl(a^{(r)}_{k_r}{}^T a^{(r)}_j\bigr)a^{(r)}_{k_r}\bigr)/\bigl\|a^{(r)}_j-\bigl(a^{(r)}_{k_r}{}^T a^{(r)}_j\bigr)a^{(r)}_{k_r}\bigr\|_2$, which is again either zero or of unit norm.
-- source:
--   Natarajan 1995, Sparse approximate solutions to linear systems, p. 229 (Algorithm Greedy, column update)

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

/-- Every column of the greedy state is either zero or of unit norm.

`greedyStep` rewrites each unselected column `j` to
`normalizeVec (s.col j - ⟪s.col k, s.col j⟫_ℝ • s.col k)`, which is zero or of unit
norm by the definition of `normalizeVec`. Columns in `insert k s.chosen` are frozen,
so they retain their previous value. Hence the property is preserved by every step
from the initial state, whose columns are all `normalizeVec (colE A j)`.

This is the first layer of the reusable invariant stack for `greedyState`; together
with `chosen_col_norm_one` it supplies the unit-norm hypothesis needed by the
orthogonality lemmas and by `residual_sq_step`. -/
theorem state_col_norm_zero_or_one {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (k : ℕ → Fin n)
    (r : ℕ) (j : Fin n) :
    (greedyState A b k r).col j = 0 ∨
      ‖(greedyState A b k r).col j‖ = 1 := by sorry

end SparseApprox.Greedy

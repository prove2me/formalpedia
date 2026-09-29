-- Prove2me | Theorems.Thm_SparseApprox_Greedy_chosen_col_norm_one
-- name    : SparseApprox.Greedy.chosen_col_norm_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T22:56:17.77372+00:00
-- url     : https://prove2.me/theorems/be0d2fb7-5e41-428e-8c3f-eef9d4074488
-- title:
--   Core invariant — every already-chosen column of the greedy state has unit norm
-- statement:
--   Let $a^{(r)}_1,\dots,a^{(r)}_n$ be the columns of $A^{(r)}$ and let $\tau^{(r)}$ be the set of indices selected so far, in the selection phase of Algorithm Greedy. If $k_0,\dots,k_{t-1}$ is a run of $t$ iterations, then for every $r\le t$ and every $i\in\tau^{(r)}$ one has $\|a^{(r)}_i\|_2=1$.
--
--   Indeed, $i$ entered $\tau$ at some step $s<r$, so $i=k_s$; at that step the run condition $a^{(s)}_{k_s}{}^T b^{(s)}\neq 0$ rules out $a^{(s)}_{k_s}=0$, and $a^{(s)}_{k_s}$ was itself produced by normalising a nonzero vector, so it has unit norm. Columns already in $\tau$ are never modified again, so the norm is still one at stage $r$.
-- source:
--   Natarajan 1995, Sparse approximate solutions to linear systems, p. 229 (Algorithm Greedy)

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm
import Theorems.Thm_SparseApprox_Greedy_state_col_norm_zero_or_one

open scoped InnerProductSpace

namespace SparseApprox.Greedy

/-- Every column whose index is already in the chosen set has unit norm.

For `r < t` the selected column `k r` cannot be zero, because the run condition
requires `⟪col_r (k r), res_r⟫_ℝ ≠ 0`; combined with
`state_col_norm_zero_or_one` this forces `‖col_r (k r)‖ = 1`. A column that is chosen
at some step is frozen from then on, so its norm stays one for every later state.
Together with `chosen_col_norm_zero_or_one` this yields unit norm for every member of
`chosen_r`, which is the hypothesis needed by the orthogonality lemmas. -/
theorem chosen_col_norm_one {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ)
    (k : ℕ → Fin n) (t r : ℕ)
    (hrun : IsGreedyRun A b ε k t) (hr : r ≤ t)
    {i : Fin n}
    (hi : i ∈ (greedyState A b k r).chosen) :
    ‖(greedyState A b k r).col i‖ = 1 := by sorry

end SparseApprox.Greedy

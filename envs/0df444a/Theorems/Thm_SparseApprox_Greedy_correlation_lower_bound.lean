-- Prove2me | Theorems.Thm_SparseApprox_Greedy_correlation_lower_bound
-- name    : SparseApprox.Greedy.correlation_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:21:05.39016+00:00
-- url     : https://prove2.me/theorems/57eb3804-e615-41fd-a746-40d52fbee3fb
-- title:
--   Eq. (12) — $\|A^{(r)T}b^{(r)}\|_\infty \ge \|b^{(r)}\|_2^2/(2\sqrt{N^{(r)}}\|u^{(r)}\|_2)$
-- statement:
--   Throughout, $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$ and $\varepsilon>0$ are the input of Algorithm Greedy, and $k_0,k_1,\dots$ are the indices it selects. For $r<t$, $A^{(r)}$ (columns $a^{(r)}_j$), $b^{(r)}$ and $\tau^{(r)}$ are the columns, the vector $b$ and the set of chosen indices at the start of iteration $r$ of a run of $t$ selection iterations, as computed by the algorithm.
--
--   Let $r<t$ and let $u^{(r)}$ be a vector with the minimum number $N^{(r)}$ of nonzero entries such that $\|A^{(r)}u^{(r)}-b^{(r)}\|_2\le\varepsilon/2$. Then some column of $A^{(r)}$ is well correlated with $b^{(r)}$:
--   $$\|A^{(r)T}b^{(r)}\|_\infty=\max_{1\le j\le n}|a_j^{(r)T}b^{(r)}|\ \ge\ \frac{\|b^{(r)}\|_2^2}{2\sqrt{N^{(r)}}\,\|u^{(r)}\|_2}.$$
--
--   This lower bound on the best correlation drives the per-iteration decrease of $\|b^{(r)}\|_2$ in the proof of Lemma 1.
--
--   **Formalization Note** The inequality is stated without division, as the existence of an index $j$ with $\|b^{(r)}\|_2^2\le 2\sqrt{N^{(r)}}\,\|u^{(r)}\|_2\,|a_j^{(r)T}b^{(r)}|$; the maximum ranges over all columns, including those already chosen.
-- source:
--   Natarajan, Sparse Approximate Solutions to Linear Systems, SIAM J. Comput. 24 (1995), p. 231, Eq. (12) (derived on p. 230 from (4)–(11), proof of Lemma 1)

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

theorem correlation_lower_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (hε : 0 < ε) (k : ℕ → Fin n) (t : ℕ)
    (hrun : IsGreedyRun A b ε k t) (r : ℕ) (hr : r < t) (u : EuclideanSpace ℝ (Fin n))
    (hu : IsMinSparseSol (greedyState A b k r).col (greedyState A b k r).res (ε / 2) u) :
    ∃ j : Fin n, ‖(greedyState A b k r).res‖ ^ 2 ≤
      2 * Real.sqrt (nnz u) * ‖u‖ * |⟪(greedyState A b k r).col j, (greedyState A b k r).res⟫_ℝ| := by sorry

end SparseApprox.Greedy

-- Prove2me | Theorems.Thm_SparseApprox_Greedy_residual_contraction
-- name    : SparseApprox.Greedy.residual_contraction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:21:37.70082+00:00
-- url     : https://prove2.me/theorems/e9cb0461-ea55-4e12-995e-ba3e0aa59236
-- title:
--   Eq. (18) — $\|b^{(r+1)}\|_2^2 \le (1-1/\rho)\|b^{(r)}\|_2^2$
-- statement:
--   Throughout, $A\in\mathbb R^{m\times n}$, $b\in\mathbb R^m$ and $\varepsilon>0$ are the input of Algorithm Greedy, and $k_0,k_1,\dots$ are the indices it selects. For $r<t$, $A^{(r)}$ (columns $a^{(r)}_j$), $b^{(r)}$ and $\tau^{(r)}$ are the columns, the vector $b$ and the set of chosen indices at the start of iteration $r$ of a run of $t$ selection iterations, as computed by the algorithm.
--
--   Let $r<t$, let $u^{(r)}$ be a minimum-support vector with $\|A^{(r)}u^{(r)}-b^{(r)}\|_2\le\varepsilon/2$ and $N^{(r)}$ nonzero entries, and let $\rho$ be a real number with
--   $$4\,N^{(r)}\,\|u^{(r)}\|_2^2\le\rho\,\|b^{(r)}\|_2^2$$
--   (the paper's $\rho=4\max_{0\le r<t}N^{(r)}\|u^{(r)}\|_2^2/\|b^{(r)}\|_2^2$ of (2) is such a number). Then one greedy iteration contracts the squared norm of $b$:
--   $$\|b^{(r+1)}\|_2^2\le\Big(1-\frac1\rho\Big)\|b^{(r)}\|_2^2 .$$
--
--   Iterating this contraction gives the logarithmic iteration bound of Lemma 1.
--
--   **Formalization Note** The conclusion is stated multiplied by $\rho$, as $\rho\,\|b^{(r+1)}\|_2^2\le(\rho-1)\|b^{(r)}\|_2^2$, so that no division by $\rho$ occurs (the two forms agree for $\rho>0$, which the hypothesis forces). The hypothesis on $\rho$ is required only at iteration $r$.
-- source:
--   Natarajan, Sparse Approximate Solutions to Linear Systems, SIAM J. Comput. 24 (1995), p. 231, Eq. (18) (from (13)–(17), proof of Lemma 1)

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

theorem residual_contraction {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (hε : 0 < ε) (k : ℕ → Fin n) (t : ℕ)
    (hrun : IsGreedyRun A b ε k t) (r : ℕ) (hr : r < t) (u : EuclideanSpace ℝ (Fin n))
    (hu : IsMinSparseSol (greedyState A b k r).col (greedyState A b k r).res (ε / 2) u)
    (ρ : ℝ) (hρ : 4 * (nnz u : ℝ) * ‖u‖ ^ 2 ≤ ρ * ‖(greedyState A b k r).res‖ ^ 2) :
    ρ * ‖(greedyState A b k (r + 1)).res‖ ^ 2 ≤ (ρ - 1) * ‖(greedyState A b k r).res‖ ^ 2 := by sorry

end SparseApprox.Greedy

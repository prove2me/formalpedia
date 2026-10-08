-- Prove2me | Theorems.Thm_Pegasos_Analysis_subgrad_bound_no_projection
-- name    : Pegasos.Analysis.subgrad_bound_no_projection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:18:11.571794+00:00
-- url     : https://prove2.me/theorems/562261b5-e441-4932-a83f-008853586ea2
-- title:
--   Proof of Theorem 1 — without projection, ‖w_{t+1}‖ ≤ R/λ and ‖∇_t‖ ≤ 2R
-- statement:
--   Let $\lambda > 0$, $k \ge 1$, labels $y_i\in\{+1,-1\}$ and $\|x_i\|\le R$ for every example. Run mini-batch Pegasos (Fig. 2) **without** the projection step, on any sequence of mini-batches. Then for every $t\ge1$
--   $$\|w_{t+1}\| \le \frac{R}{\lambda}\qquad\text{and}\qquad\|\nabla_t\|\le 2R,$$
--   where $\nabla_t$ is the sub-gradient (8) at $w_t$ on the batch $A_t$.
--
--   This is the gradient bound $G = 2R$ that Lemma 1 needs in the unprojected case (with $B = \mathbb R^n$).
--
--   **Formalization Note.** Iterations are 1-based with $w_1 = 0$; mini-batches are $k$-tuples of indices and the statement holds for every sequence of them.
-- source:
--   Shalev-Shwartz, Singer, Srebro & Cotter, Pegasos: primal estimated sub-gradient solver for SVM, Math. Program. 127 (2011), p. 11, proof of Theorem 1

import Mathlib
import Definitions.Def_Pegasos_Analysis_Model

namespace Pegasos.Analysis

/-- **Proof of Theorem 1** (p. 11): without the projection step, for every `t ≥ 1`,
`‖w_{t+1}‖ ≤ R/λ` and the sub-gradient (8) at `w_t` on `A_t` satisfies `‖∇_t‖ ≤ 2R`. -/
theorem subgrad_bound_no_projection {n m k : ℕ} (lam R : ℝ) (hlam : 0 < lam) (hk : 0 < k)
    (x : Fin m → EuclideanSpace ℝ (Fin n)) (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (hR : ∀ i, ‖x i‖ ≤ R) (A : ℕ → Fin k → Fin m) (t : ℕ) (ht : 1 ≤ t) :
    ‖run lam x y A false (t + 1)‖ ≤ R / lam ∧
      ‖subgrad lam x y (A t) (run lam x y A false t)‖ ≤ 2 * R := by sorry

end Pegasos.Analysis

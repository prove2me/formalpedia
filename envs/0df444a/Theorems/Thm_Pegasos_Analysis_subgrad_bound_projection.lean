-- Prove2me | Theorems.Thm_Pegasos_Analysis_subgrad_bound_projection
-- name    : Pegasos.Analysis.subgrad_bound_projection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:17:59.063403+00:00
-- url     : https://prove2.me/theorems/a2aff8ff-176b-47cf-b71d-f204f7c9c8b2
-- title:
--   Proof of Theorem 1 — with projection, ‖w_t‖ ≤ 1/√λ and ‖∇_t‖ ≤ √λ + R
-- statement:
--   Let $\lambda > 0$, $k \ge 1$, labels $y_i\in\{+1,-1\}$ and $\|x_i\|\le R$ for every example. Run mini-batch Pegasos (Fig. 2) **with** the projection step, on any sequence of mini-batches $A_1, A_2, \dots$. Then for every $t\ge1$
--   $$\|w_t\| \le \frac{1}{\sqrt\lambda}\qquad\text{and}\qquad \|\nabla_t\| \le \sqrt\lambda + R,$$
--   where $\nabla_t = \lambda w_t - \frac1k\sum_{i\in A_t}\mathbb 1[y_i\langle w_t,x_i\rangle<1]\,y_ix_i$ is the sub-gradient (8).
--
--   This is the gradient bound $G = \sqrt\lambda + R$ that Lemma 1 needs in the projected case.
--
--   **Formalization Note.** Iterations are 1-based with $w_1 = 0$; mini-batches are $k$-tuples of indices and the statement holds for every sequence of them.
-- source:
--   Shalev-Shwartz, Singer, Srebro & Cotter, Pegasos: primal estimated sub-gradient solver for SVM, Math. Program. 127 (2011), p. 11, proof of Theorem 1

import Mathlib
import Definitions.Def_Pegasos_Analysis_Model

namespace Pegasos.Analysis

/-- **Proof of Theorem 1** (p. 11): with the projection step, every iterate satisfies
`‖w_t‖ ≤ 1/√λ`, and hence the sub-gradient (8) at `w_t` on `A_t` satisfies
`‖∇_t‖ ≤ √λ + R`, for every `t ≥ 1`. -/
theorem subgrad_bound_projection {n m k : ℕ} (lam R : ℝ) (hlam : 0 < lam) (hk : 0 < k)
    (x : Fin m → EuclideanSpace ℝ (Fin n)) (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (hR : ∀ i, ‖x i‖ ≤ R) (A : ℕ → Fin k → Fin m) (t : ℕ) (ht : 1 ≤ t) :
    ‖run lam x y A true t‖ ≤ 1 / Real.sqrt lam ∧
      ‖subgrad lam x y (A t) (run lam x y A true t)‖ ≤ Real.sqrt lam + R := by sorry

end Pegasos.Analysis

-- Prove2me | Theorems.Thm_Pegasos_Analysis_eq_13
-- name    : Pegasos.Analysis.eq_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:18:30.12727+00:00
-- url     : https://prove2.me/theorems/eba06a3f-113a-460d-8f2e-b539c6c06fb1
-- title:
--   Eq. (13) — without projection, w_{t+1} = (1/(λt)) Σ_{i≤t} v_i
-- statement:
--   Let $\lambda>0$ and run mini-batch Pegasos (Fig. 2) **without** the projection step, on any sequence of mini-batches $A_1, A_2,\dots$ of $k$ indices. Write
--   $$v_i = \frac{1}{k}\sum_{j\in A_i}\mathbb 1\bigl[y_j\langle w_i, x_j\rangle < 1\bigr]\, y_j x_j .$$
--   Then for every $t\ge1$
--   $$w_{t+1} = \frac{1}{\lambda t}\sum_{i=1}^t v_i .$$
--
--   Writing the unprojected iterate as an average of margin-violation vectors is what yields the norm bound $\|w_{t+1}\|\le R/\lambda$.
--
--   **Formalization Note.** The paper's intermediate display (12) is printed as $w_{t+1} = (1-\frac1t)w_t - \frac{1}{t\lambda}v_t$ with $x_t$ inside the indicator; since $\nabla_t = \lambda w_t - v_t$ the correct update is $w_{t+1} = (1-\frac1t)w_t + \frac{1}{t\lambda}v_t$ with $x_j$ in the indicator. Eq. (13) is correct as printed and is what is stated. Iterations are 1-based with $w_1 = 0$.
-- source:
--   Shalev-Shwartz, Singer, Srebro & Cotter, Pegasos: primal estimated sub-gradient solver for SVM, Math. Program. 127 (2011), p. 11, Eq. (13) (proof of Theorem 1)

import Mathlib
import Definitions.Def_Pegasos_Analysis_Model

namespace Pegasos.Analysis

/-- **Eq. (13)** (p. 11): without the projection step, for every `t ≥ 1`,
`w_{t+1} = (1/(λt)) Σ_{i=1}^t v_i` with `v_i = (1/k) Σ_{j∈A_i} 1l[y_j⟨w_i, x_j⟩ < 1] y_j x_j`. -/
theorem eq_13 {n m k : ℕ} (lam : ℝ) (hlam : 0 < lam)
    (x : Fin m → EuclideanSpace ℝ (Fin n)) (y : Fin m → ℝ) (A : ℕ → Fin k → Fin m)
    (t : ℕ) (ht : 1 ≤ t) :
    run lam x y A false (t + 1)
      = (1 / (lam * (t : ℝ))) • ∑ i ∈ Finset.Icc 1 t, hingeTerm x y (A i) (run lam x y A false i) := by sorry

end Pegasos.Analysis

-- Prove2me | Theorems.Thm_Pegasos_Analysis_projBall_isProj
-- name    : Pegasos.Analysis.projBall_isProj
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:18:07.071494+00:00
-- url     : https://prove2.me/theorems/d661b511-204d-4621-92ca-5c95b4205640
-- title:
--   Proof of Theorem 1 — the projection step (6) is Π_B onto the ball of radius 1/√λ
-- statement:
--   Let $\lambda > 0$ and let $B = \{w\in\mathbb R^n : \|w\|\le 1/\sqrt\lambda\}$. For every $v\in\mathbb R^n$, the point
--   $$\min\Bigl\{1, \frac{1/\sqrt\lambda}{\|v\|}\Bigr\}\, v$$
--   produced by the projection step (6) is the Euclidean projection $\Pi_B(v)$: it lies in $B$ and is at least as close to $v$ as every point of $B$.
--
--   This lets the projected Pegasos update be written as $w_{t+1} = \Pi_B(w_t - \eta_t\nabla_t)$, the form Lemma 1 requires.
--
--   **Formalization Note.** At $v = 0$ the formula is undefined on paper; Lean's $a/0 = 0$ gives $0$, which is the projection of $0$.
-- source:
--   Shalev-Shwartz, Singer, Srebro & Cotter, Pegasos: primal estimated sub-gradient solver for SVM, Math. Program. 127 (2011), p. 11, proof of Theorem 1 (with Eq. (6), p. 8)

import Mathlib
import Definitions.Def_Pegasos_Analysis_Model

namespace Pegasos.Analysis

/-- **Proof of Theorem 1** (p. 11): the projection step (6), `w ↦ min{1, (1/√λ)/‖w‖} w`,
is the Euclidean projection `Π_B` onto the closed ball `B` of radius `1/√λ` centred at 0. -/
theorem projBall_isProj {n : ℕ} (lam : ℝ) (hlam : 0 < lam) (v : EuclideanSpace ℝ (Fin n)) :
    LogRegretOCO.OGD.IsProj (Metric.closedBall 0 (1 / Real.sqrt lam)) v (projBall lam v) := by sorry

end Pegasos.Analysis

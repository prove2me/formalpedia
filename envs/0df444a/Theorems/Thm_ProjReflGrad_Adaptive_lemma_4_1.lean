-- Prove2me | Theorems.Thm_ProjReflGrad_Adaptive_lemma_4_1
-- name    : ProjReflGrad.Adaptive.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:15:39.165581+00:00
-- url     : https://prove2.me/theorems/834fda11-0928-4c6f-9fb5-e749579f32a1
-- title:
--   Lemma 4.1, p. 9 — step (4.i) of the adaptive projected reflected gradient method is well-defined
-- statement:
--   Let $F : H \to H$, $\alpha \ge 0$, $\bar\lambda \in \mathbb R$, and let the previous data of Algorithm 4.2 be a reflection $y_{n-1}$, a weight $\tau_{n-1}$ and a step $\lambda_{n-1} > 0$. Let $\hat y$ be the trial reflection and $\hat\lambda = \lambda(\hat y, 1)$ the trial step of (4.1). If $\hat\lambda \ge \lambda_{n-1}$, then there is $\lambda'_n \in [\lambda_{n-1}, \hat\lambda]$ with
--   $$\|\lambda'_n F(\hat y) - \lambda_{n-1}F(y_{n-1})\| \le \alpha\|\hat y - y_{n-1}\|. \qquad (4.2)$$
--
--   This is Lemma 4.1: the choice required in step (4.i) of Algorithm 4.2 is always possible.
--
--   **Formalization Note** The statement is phrased on the data of one step; $\lambda(\cdot,\cdot)$ is the step rule of the setting with the convention $0/0 = +\infty$. The hypothesis $\alpha \ge 0$ is part of the standing range $\alpha \in (0, \sqrt2 - 1)$.
-- source:
--   Malitsky, Projected Reflected Gradient Methods for Monotone Variational Inequalities, arXiv:1502.04968v1, p. 9, Lemma 4.1

import Mathlib
import Definitions.Def_ProjReflGrad_Adaptive_Setting

namespace ProjReflGrad.Adaptive

/-- Lemma 4.1 (Malitsky 2015, p. 9): step (4.i) of Algorithm 4.2 is well-defined. If the trial
step `λ(ŷ, 1)` (computed from the previous data `yp, taup, lamp`) is at least `λ_{n-1} = lamp > 0`,
then some `λ'_n ∈ [λ_{n-1}, λ(ŷ, 1)]` satisfies (4.2). -/
theorem lemma_4_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (F : H → H) (α lamBar : ℝ) (hα : 0 ≤ α)
    (yp yh : H) (taup lamp : ℝ) (hlamp : 0 < lamp)
    (hge : lamp ≤ stepCap F α lamBar yp taup lamp yh 1) :
    ∃ l ∈ Set.Icc lamp (stepCap F α lamBar yp taup lamp yh 1),
      ‖l • F yh - lamp • F yp‖ ≤ α * ‖yh - yp‖ := by sorry

end ProjReflGrad.Adaptive

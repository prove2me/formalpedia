-- Prove2me | Theorems.Thm_ProjReflGrad_Adaptive_lemma_4_2
-- name    : ProjReflGrad.Adaptive.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:15:29.81772+00:00
-- url     : https://prove2.me/theorems/58b6d8f9-b580-4775-a119-ddd01f502a42
-- title:
--   Lemma 4.2, p. 9 — step (4.ii) of the adaptive projected reflected gradient method is well-defined
-- statement:
--   Let $F : H \to H$ be $L$-Lipschitz with $L > 0$, let $\alpha > 0$, and let the previous data of Algorithm 4.2 be points $x_n, x_{n-1}, y_{n-1}$, a weight $\tau_{n-1} \ge 0$ and a step $\lambda_{n-1}$ with $0 < \lambda_{n-1} \le \bar\lambda$. For $\tau \in (0,1]$ write $y'(\tau) = x_n + \tau(x_n - x_{n-1})$ and let $\lambda(\cdot,\cdot)$ be the step rule (4.1). Then there is $\tau'_n \in (0, 1]$ with
--   $$\lambda(y'(\tau'_n), \tau'_n) \ge \tau'_n\lambda_{n-1} \qquad (4.3)$$
--   and there is $\lambda'_n \in [\tau'_n\lambda_{n-1}, \lambda(y'(\tau'_n), \tau'_n)]$ with
--   $$\|\lambda'_n F(y'(\tau'_n)) - \tau'_n\lambda_{n-1}F(y_{n-1})\| \le \alpha\|y'(\tau'_n) - y_{n-1}\|. \qquad (4.4)$$
--
--   This is Lemma 4.2: the choices required in step (4.ii) of Algorithm 4.2 are always possible. Along every run the hypotheses $0 < \lambda_{n-1} \le \bar\lambda$ and $\tau_{n-1} \in (0,1]$ hold, so the lemma applies at every step.
--
--   **Formalization Note** The statement does not assume $\bar\lambda \ge \alpha/L$ or $\lambda_{n-1} \ge \alpha/L$. The paper's proof takes $\tau'_n = \alpha/(\lambda_{n-1}L)$, which lies in $(0,1]$ only when $\lambda_{n-1} \ge \alpha/L$; the statement as printed holds without that bound. It also does not assume the branch condition $\hat\lambda_n < \lambda_{n-1}$, which the conclusion does not need.
-- source:
--   Malitsky, Projected Reflected Gradient Methods for Monotone Variational Inequalities, arXiv:1502.04968v1, p. 9, Lemma 4.2

import Mathlib
import Definitions.Def_ProjReflGrad_Adaptive_Setting

namespace ProjReflGrad.Adaptive

/-- Lemma 4.2 (Malitsky 2015, p. 9): step (4.ii) of Algorithm 4.2 is well-defined. For an
`L`-Lipschitz `F`, `α > 0` and previous data `0 < λ_{n-1} ≤ λ̄`, `τ_{n-1} ≥ 0`, some
`τ'_n ∈ (0, 1]` satisfies (4.3) for `y'_n = x_n + τ'_n (x_n - x_{n-1})`, and then some
`λ'_n ∈ [τ'_n λ_{n-1}, λ(y'_n, τ'_n)]` satisfies (4.4). -/
theorem lemma_4_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (F : H → H) (L : ℝ) (hL : 0 < L)
    (hC3 : ProjReflGrad.Weak.IsLipschitzMap F L) (α lamBar : ℝ) (hα : 0 < α) (xn xp yp : H) (taup lamp : ℝ)
    (htaup : 0 ≤ taup) (hlamp : 0 < lamp) (hlampBar : lamp ≤ lamBar) :
    ∃ τ ∈ Set.Ioc (0 : ℝ) 1,
      τ * lamp ≤ stepCap F α lamBar yp taup lamp (xn + τ • (xn - xp)) τ ∧
      ∃ l ∈ Set.Icc (τ * lamp) (stepCap F α lamBar yp taup lamp (xn + τ • (xn - xp)) τ),
        ‖l • F (xn + τ • (xn - xp)) - (τ * lamp) • F yp‖
          ≤ α * ‖(xn + τ • (xn - xp)) - yp‖ := by sorry

end ProjReflGrad.Adaptive

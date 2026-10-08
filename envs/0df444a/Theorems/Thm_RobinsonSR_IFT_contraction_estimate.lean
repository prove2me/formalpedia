-- Prove2me | Theorems.Thm_RobinsonSR_IFT_contraction_estimate
-- name    : RobinsonSR.IFT.contraction_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:59:44.266759+00:00
-- url     : https://prove2.me/theorems/16e4274b-57d0-4d42-b149-7f5f197d87c0
-- title:
--   Proof of Theorem 2.1, p. 46 — ‖Φ_p(x₁) − Φ_p(x₂)‖ ≤ λδ‖x₁ − x₂‖ on V_ε
-- statement:
--   Let $X$ be a real normed space, $\Omega\subseteq X$, $P$ a set, $p_0\in P$, $x_0\in X$, and $f:P\times X\to X'$ such that for every $p$ and every $x\in\Omega$ the map $f(p,\cdot)$ is Fréchet differentiable at $x$ with derivative $f'(p,x)$. Let $U\subseteq X'$ and $s:X'\to X$ with
--   $$\|s(y_1)-s(y_2)\|\le\lambda\|y_1-y_2\|\qquad (y_1,y_2\in U),$$
--   where $\lambda\ge0$. Let $V_\varepsilon$ be the closed ball of radius $\rho$ about $x_0$, contained in $\Omega$, and fix $p\in P$ and $\delta>0$ such that for every $x\in V_\varepsilon$ one has $r(p,x)\in U$ and $\|f'(p,x)-f'(p_0,x_0)\|\le\delta$, where $r(p,x)=f(p_0,x_0)+f'(p_0,x_0)(x-x_0)-f(p,x)$. With $\Phi_p(x):=s(r(p,x))$, for all $x_1,x_2\in V_\varepsilon$,
--   $$\|\Phi_p(x_1)-\Phi_p(x_2)\|\le\lambda\delta\|x_1-x_2\|.$$
--
--   Since $\lambda\delta<1$ in the proof of Theorem 2.1, this makes $\Phi_p$ a strong contraction on $V_\varepsilon$.
--
--   **Formalization Note** $\lambda\ge0$ is implicit on the page (it is a Lipschitz modulus, and the proof chooses $\lambda\delta<\varepsilon/(\lambda+\varepsilon)$); it is stated explicitly. The hypothesis $V_\varepsilon\subseteq V$ of the page is not needed for this estimate and is not assumed.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), p. 46, proof of Theorem 2.1, display ‖Φ_p(x₁) − Φ_p(x₂)‖ ≤ … ≤ λδ‖x₁ − x₂‖

import Mathlib
import Definitions.Def_RobinsonSR_IFT_Setting

namespace RobinsonSR.IFT

/-- Proof of Theorem 2.1, p. 46: `‖Φ_p(x₁) − Φ_p(x₂)‖ ≤ λδ‖x₁ − x₂‖` on `V_ε`, where
`Φ_p(x) = s (r(p, x))`. -/
theorem contraction_estimate {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Ω : Set X) {P : Type*} (p0 : P) (x0 : X)
    (f : P → X → StrongDual ℝ X) (f' : P → X → (X →L[ℝ] StrongDual ℝ X))
    (hf' : ∀ p, ∀ x ∈ Ω, HasFDerivAt (f p) (f' p x) x)
    (U : Set (StrongDual ℝ X)) (s : StrongDual ℝ X → X) (lam : ℝ) (hlam : 0 ≤ lam)
    (hsL : ∀ y₁ ∈ U, ∀ y₂ ∈ U, ‖s y₁ - s y₂‖ ≤ lam * ‖y₁ - y₂‖)
    (rho delta : ℝ) (hdelta0 : 0 < delta) (hballΩ : Metric.closedBall x0 rho ⊆ Ω) (p : P)
    (hU : ∀ x ∈ Metric.closedBall x0 rho, residual f f' p0 x0 p x ∈ U)
    (hdelta : ∀ x ∈ Metric.closedBall x0 rho, ‖f' p x - f' p0 x0‖ ≤ delta) :
    ∀ x₁ ∈ Metric.closedBall x0 rho, ∀ x₂ ∈ Metric.closedBall x0 rho,
      ‖s (residual f f' p0 x0 p x₁) - s (residual f f' p0 x0 p x₂)‖ ≤
        lam * delta * ‖x₁ - x₂‖ := by sorry

end RobinsonSR.IFT

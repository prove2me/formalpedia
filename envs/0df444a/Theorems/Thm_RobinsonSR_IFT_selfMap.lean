-- Prove2me | Theorems.Thm_RobinsonSR_IFT_selfMap
-- name    : RobinsonSR.IFT.selfMap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:59:49.294587+00:00
-- url     : https://prove2.me/theorems/21720b8f-2b8b-45f4-aaf5-f402b687bb79
-- title:
--   Proof of Theorem 2.1, p. 46 — Φ_p is a self-map of the closed ball V_ε
-- statement:
--   Let $X$ be a real normed space, $C,\Omega\subseteq X$, $P$ a set, $p_0\in P$, $x_0\in X$, and $f:P\times X\to X'$ with $f(p,\cdot)$ Fréchet differentiable at every $x\in\Omega$ with derivative $f'(p,x)$. Suppose $x_0$ solves $0\in f(p_0,x)+\partial\psi_C(x)$. Let $U\subseteq X'$ with $0\in U$, $V\subseteq X$, and $s:X'\to X$ be the single-valued localisation of $L^{-1}$, with $L(x)=f(p_0,x_0)+f'(p_0,x_0)(x-x_0)+\partial\psi_C(x)$: for $y\in U$, $s(y)\in V$ is the unique $z\in V$ with $y\in L(z)$; and suppose $s$ is Lipschitzian on $U$ with modulus $\lambda\ge0$. Let $\rho>0$, $\delta>0$ with $\lambda\delta<1$, let $V_\varepsilon$ be the closed ball of radius $\rho$ about $x_0$ with $V_\varepsilon\subseteq V\cap\Omega$, and let $p\in P$ satisfy, for all $x\in V_\varepsilon$, $r(p,x)\in U$ and $\|f'(p,x)-f'(p_0,x_0)\|\le\delta$, together with
--   $$\lambda\|f(p_0,x_0)-f(p,x_0)\|\le(1-\lambda\delta)\rho .$$
--   Then $\Phi_p(x):=s(r(p,x))$ maps $V_\varepsilon$ into itself:
--   $$\|\Phi_p(x)-x_0\|\le\rho\qquad\text{for all }x\in V_\varepsilon .$$
--
--   Together with the contraction estimate this puts $\Phi_p$ in the setting of the contraction principle.
--
--   **Formalization Note** The page's "$x_0=V\cap L^{-1}(0)$" is not assumed; it follows from $0\in U$, $x_0\in V$ and $x_0$ solving the unperturbed equation, which are assumed. $\lambda\ge0$ is implicit on the page and stated explicitly.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), p. 46, proof of Theorem 2.1, displays bounding ‖Φ_p(x₀) − x₀‖ and ‖Φ_p(x) − x₀‖

import Mathlib
import Definitions.Def_RobinsonSR_IFT_Setting

namespace RobinsonSR.IFT

/-- Proof of Theorem 2.1, p. 46: `Φ_p(x) = s (r(p, x))` maps the closed ball `V_ε` of radius `ρ`
about `x₀` into itself. -/
theorem selfMap {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set X) (Ω : Set X) {P : Type*} (p0 : P) (x0 : X)
    (f : P → X → StrongDual ℝ X) (f' : P → X → (X →L[ℝ] StrongDual ℝ X))
    (hf' : ∀ p, ∀ x ∈ Ω, HasFDerivAt (f p) (f' p x) x)
    (hsol : -(f p0 x0) ∈ normalCone C x0)
    (U : Set (StrongDual ℝ X)) (V : Set X) (s : StrongDual ℝ X → X)
    (hs : ∀ y ∈ U, s y ∈ V ∧ y - (f p0 x0 + f' p0 x0 (s y - x0)) ∈ normalCone C (s y) ∧
      ∀ z ∈ V, y - (f p0 x0 + f' p0 x0 (z - x0)) ∈ normalCone C z → z = s y)
    (hU0 : (0 : StrongDual ℝ X) ∈ U)
    (lam : ℝ) (hlam : 0 ≤ lam)
    (hsL : ∀ y₁ ∈ U, ∀ y₂ ∈ U, ‖s y₁ - s y₂‖ ≤ lam * ‖y₁ - y₂‖)
    (rho delta : ℝ) (hrho : 0 < rho) (hdelta0 : 0 < delta) (hlamdelta : lam * delta < 1)
    (hball : Metric.closedBall x0 rho ⊆ V ∩ Ω) (p : P)
    (hU : ∀ x ∈ Metric.closedBall x0 rho, residual f f' p0 x0 p x ∈ U)
    (hdelta : ∀ x ∈ Metric.closedBall x0 rho, ‖f' p x - f' p0 x0‖ ≤ delta)
    (hN : lam * ‖f p0 x0 - f p x0‖ ≤ (1 - lam * delta) * rho) :
    ∀ x ∈ Metric.closedBall x0 rho,
      s (residual f f' p0 x0 p x) ∈ Metric.closedBall x0 rho := by sorry

end RobinsonSR.IFT

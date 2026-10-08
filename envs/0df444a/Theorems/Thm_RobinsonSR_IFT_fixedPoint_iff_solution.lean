-- Prove2me | Theorems.Thm_RobinsonSR_IFT_fixedPoint_iff_solution
-- name    : RobinsonSR.IFT.fixedPoint_iff_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:59:46.337984+00:00
-- url     : https://prove2.me/theorems/e13a4596-fc6b-4cff-93e9-2c41ae24f968
-- title:
--   Proof of Theorem 2.1, p. 46 — x ∈ V_ε is a fixed point of Φ_p iff 0 ∈ f(p, x) + ∂ψ_C(x)
-- statement:
--   Let $X$ be a real normed space, $C\subseteq X$, $P$ a set, $p_0\in P$, $x_0\in X$, $f:P\times X\to X'$ and $f'(p,x)$ bounded linear operators $X\to X'$. Let $U\subseteq X'$, $V\subseteq X$, and let $s:X'\to X$ be the single-valued localisation of $L^{-1}$ on $U$, where
--   $$L(x):=f(p_0,x_0)+f'(p_0,x_0)(x-x_0)+\partial\psi_C(x):$$
--   for every $y\in U$, $s(y)\in V$, $y\in L(s(y))$, and $s(y)$ is the only point $z\in V$ with $y\in L(z)$. Let $V_\varepsilon$ be the closed ball of radius $\rho$ about $x_0$, with $V_\varepsilon\subseteq V$, and fix $p\in P$ with $r(p,x)\in U$ for all $x\in V_\varepsilon$, where $r$ is the residual. Write $\Phi_p(x):=s(r(p,x))=V\cap L^{-1}[r(p,x)]$. Then for every $x\in V_\varepsilon$,
--   $$\Phi_p(x)=x \iff 0\in f(p,x)+\partial\psi_C(x).$$
--
--   This identifies the solutions of the perturbed generalized equation in $V_\varepsilon$ with the fixed points of $\Phi_p$, which is how the proof of Theorem 2.1 obtains the solution $x(p)$.
--
--   **Formalization Note** The set-valued $\Phi_p(x)=V\cap L^{-1}[r(p,x)]$ is represented by the single-valued $s(r(p,x))$, where $s$ is an explicit function with the existence and uniqueness properties that strong regularity provides on $U$; the Lipschitz property of $s$ is not needed for this claim and is not assumed.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), p. 46, proof of Theorem 2.1, first sentence after the definition of Φ_p

import Mathlib
import Definitions.Def_RobinsonSR_IFT_Setting

namespace RobinsonSR.IFT

/-- Proof of Theorem 2.1, p. 46: with `Φ_p(x) := V ∩ L⁻¹[r(p, x)]`, realised as `s (r(p, x))`
where `s` is the single-valued localisation of `L⁻¹` given by strong regularity,
`x ∈ V_ε` is a fixed point of `Φ_p` iff `x ∈ V_ε` solves `0 ∈ f(p, x) + ∂ψ_C(x)`. -/
theorem fixedPoint_iff_solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set X) {P : Type*} (p0 : P) (x0 : X)
    (f : P → X → StrongDual ℝ X) (f' : P → X → (X →L[ℝ] StrongDual ℝ X))
    (U : Set (StrongDual ℝ X)) (V : Set X) (s : StrongDual ℝ X → X)
    (hs : ∀ y ∈ U, s y ∈ V ∧ y - (f p0 x0 + f' p0 x0 (s y - x0)) ∈ normalCone C (s y) ∧
      ∀ z ∈ V, y - (f p0 x0 + f' p0 x0 (z - x0)) ∈ normalCone C z → z = s y)
    (rho : ℝ) (hball : Metric.closedBall x0 rho ⊆ V) (p : P)
    (hU : ∀ x ∈ Metric.closedBall x0 rho, residual f f' p0 x0 p x ∈ U) :
    ∀ x ∈ Metric.closedBall x0 rho,
      (s (residual f f' p0 x0 p x) = x ↔ -(f p x) ∈ normalCone C x) := by sorry

end RobinsonSR.IFT

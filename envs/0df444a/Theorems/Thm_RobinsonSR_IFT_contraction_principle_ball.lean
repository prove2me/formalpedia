-- Prove2me | Theorems.Thm_RobinsonSR_IFT_contraction_principle_ball
-- name    : RobinsonSR.IFT.contraction_principle_ball
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:44:19.098373+00:00
-- url     : https://prove2.me/theorems/4b88af4d-424e-48e2-86f3-066104ea0078
-- title:
--   Proof of Theorem 2.1, p. 46 — contraction principle on V_ε with the bound (2.5): ‖x(p) − x‖ ≤ (1 − λδ)⁻¹‖Φ_p(x) − x‖
-- statement:
--   Let $X$ be a real Banach space, $x_0\in X$, $\rho>0$, and $V_\varepsilon$ the closed ball of radius $\rho$ about $x_0$. Let $\Phi:X\to X$ map $V_\varepsilon$ into itself and satisfy, for some $\kappa$ with $0\le\kappa<1$,
--   $$\|\Phi(x_1)-\Phi(x_2)\|\le\kappa\|x_1-x_2\|\qquad(x_1,x_2\in V_\varepsilon).$$
--   Then $\Phi$ has a unique fixed point $x_p$ in $V_\varepsilon$, and for each $x\in V_\varepsilon$
--   $$\|x_p-x\|\le(1-\kappa)^{-1}\|\Phi(x)-x\|. \tag{2.5}$$
--
--   In the proof of Theorem 2.1 this is applied with $\Phi=\Phi_p$ and $\kappa=\lambda\delta$; the fixed point is the solution $x(p)$, and (2.5) is the bound from which (2.4) follows.
--
--   **Formalization Note** $X$ is assumed complete. The page applies the contraction principle on $V_\varepsilon$ in a space it calls only normed; on a closed ball of an incomplete space the principle can fail, so completeness is the hypothesis under which the principle, as invoked, holds. Theorem 2.1 itself is stated without completeness. The values of $\Phi$ off $V_\varepsilon$ play no role, and uniqueness is among fixed points in $V_\varepsilon$.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), p. 46, proof of Theorem 2.1, (2.5)

import Mathlib

namespace RobinsonSR.IFT

/-- Proof of Theorem 2.1, p. 46, the contraction principle as invoked there: a self-map `Φ` of
the closed ball `V_ε = closedBall x₀ ρ` (`ρ > 0`) of a Banach space that is a contraction with
modulus `κ ∈ [0, 1)` on it has a unique fixed point `x_p ∈ V_ε`, and
`‖x_p − x‖ ≤ (1 − κ)⁻¹ ‖Φ x − x‖` for every `x ∈ V_ε` (bound (2.5), with `κ = λδ`). -/
theorem contraction_principle_ball {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (x0 : X) (rho : ℝ) (hrho : 0 < rho) (Φ : X → X)
    (hmaps : Set.MapsTo Φ (Metric.closedBall x0 rho) (Metric.closedBall x0 rho))
    (kappa : ℝ) (hk0 : 0 ≤ kappa) (hk1 : kappa < 1)
    (hcontr : ∀ x₁ ∈ Metric.closedBall x0 rho, ∀ x₂ ∈ Metric.closedBall x0 rho,
      ‖Φ x₁ - Φ x₂‖ ≤ kappa * ‖x₁ - x₂‖) :
    ∃ xp ∈ Metric.closedBall x0 rho, Φ xp = xp ∧
      (∀ z ∈ Metric.closedBall x0 rho, Φ z = z → z = xp) ∧
      ∀ x ∈ Metric.closedBall x0 rho, ‖xp - x‖ ≤ (1 - kappa)⁻¹ * ‖Φ x - x‖ := by sorry

end RobinsonSR.IFT

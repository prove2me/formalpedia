-- Prove2me | Theorems.Thm_SpikedWishart_Separated_eq_218_219
-- name    : SpikedWishart.Separated.eq_218_219
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:36:40.366976+00:00
-- url     : https://prove2.me/theorems/ce9dd900-e0c5-40d8-8e57-087c054489d7
-- title:
--   (218)–(219), p. 1679 — critical points π₁ < γ/(1+γ) < 1/(μπ₁) < 1 of f, f″(π₁) = −ν² < 0, f″(1/(μπ₁)) = (γνμπ₁(1−π₁))² > 0
-- statement:
--   Let $\gamma \ge 1$ and $\pi_1 > 0$ satisfy condition (209), $\pi_1^{-1} > 1 + \gamma^{-1}$. Let $\mu$, $\nu$ be given by (211), $q \in \mathbb R$, and $f(z) = -\mu(z-q) + \log z - \gamma^{-2}\log(1-z)$ (215). Then $z = \pi_1$ and $z = 1/(\mu\pi_1)$ are critical points of $f$,
--   $$
--   \pi_1 < \frac{\gamma}{1+\gamma} < \frac1{\mu\pi_1} < 1,
--   $$
--   and
--   $$
--   f''(\pi_1) = -\nu^2 < 0, \qquad f''\Big(\frac1{\mu\pi_1}\Big) = \big(\gamma\nu\mu\pi_1(1-\pi_1)\big)^2 > 0 .
--   $$
--
--   The point $\pi_1$ is the saddle point used for $\mathcal J$, and $1/(\mu\pi_1)$ the one relevant to $\mathcal H$; the signs of the second derivatives fix the directions of steepest descent.
--
--   **Formalization Note** $f$ is a function on $\mathbb C$, and the derivatives are complex derivatives taken at the real points $\pi_1, 1/(\mu\pi_1) \in (0,1)$, where $f$ is holomorphic. The parameter $q$ does not affect the derivatives.
-- source:
--   Baik, Ben Arous and Péché, Phase transition of the largest eigenvalue for nonnull complex sample covariance matrices, Ann. Probab. 33 (2005), p. 1679, (218)–(219); assumption (209), p. 1678

import Mathlib
import Definitions.Def_SpikedWishart_Separated_Phase

namespace SpikedWishart.Separated

/-- (218)–(219), p. 1679: under (209), `π₁` and `1/(μπ₁)` are critical points of `f`,
`π₁ < γ/(1+γ) < 1/(μπ₁) < 1`, `f''(π₁) = −ν² < 0` and
`f''(1/(μπ₁)) = (γνμπ₁(1 − π₁))² > 0`. Derivatives are complex derivatives at real points. -/
theorem eq_218_219 (γ π₁ q : ℝ) (hγ : 1 ≤ γ) (hπ : 0 < π₁) (h209 : 1 + γ⁻¹ < π₁⁻¹) :
    deriv (fPhase γ π₁ q) (π₁ : ℂ) = 0 ∧
    deriv (fPhase γ π₁ q) ((1 / (mu γ π₁ * π₁) : ℝ) : ℂ) = 0 ∧
    π₁ < γ / (1 + γ) ∧ γ / (1 + γ) < 1 / (mu γ π₁ * π₁) ∧ 1 / (mu γ π₁ * π₁) < 1 ∧
    deriv (deriv (fPhase γ π₁ q)) (π₁ : ℂ) = -((nu γ π₁ : ℝ) : ℂ) ^ 2 ∧ -(nu γ π₁) ^ 2 < 0 ∧
    deriv (deriv (fPhase γ π₁ q)) ((1 / (mu γ π₁ * π₁) : ℝ) : ℂ) =
      ((γ * nu γ π₁ * mu γ π₁ * π₁ * (1 - π₁) : ℝ) : ℂ) ^ 2 ∧
    0 < (γ * nu γ π₁ * mu γ π₁ * π₁ * (1 - π₁)) ^ 2 := by sorry

end SpikedWishart.Separated

-- Prove2me | Theorems.Thm_VanderbeiLP_SelfDual_step_direction_relations
-- name    : VanderbeiLP.SelfDual.step_direction_relations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T13:53:20.113992+00:00
-- url     : https://prove2.me/theorems/a48da35a-04c9-4e1d-a6af-dc6a50078a40
-- title:
--   Theorem 22.2 — orthogonality of the step directions and the effect of a step on ρ, μ and XZe − μe
-- statement:
--   Let $n \ge 2$ and let $A$ be a real skew-symmetric $n \times n$ matrix. Let $x, z \in \mathbb{R}^n$, let $0 \le \delta \le 1$, and let $(\Delta x, \Delta z)$ be any solution of the step equations
--
--   $$A\Delta x + \Delta z = -(1 - \delta)\rho, \qquad Z\Delta x + X\Delta z = \delta\mu e - XZe, \qquad (22.5)\text{–}(22.6)$$
--
--   where $\rho = \rho(x, z) = Ax + z$ and $\mu = \mu(x, z) = \frac1n x^T z$. For a step length $\theta \in \mathbb{R}$ put $\bar x = x + \theta\Delta x$, $\bar z = z + \theta\Delta z$, $\bar\rho = \rho(\bar x, \bar z)$, $\bar\mu = \mu(\bar x, \bar z)$. Then
--
--   1. $\Delta z^T \Delta x = 0$;
--   2. $\bar\rho = (1 - \theta + \theta\delta)\rho$;
--   3. $\bar\mu = (1 - \theta + \theta\delta)\mu$;
--   4. $$\bar X\bar Ze - \bar\mu e = (1 - \theta)(XZe - \mu e) + \theta^2\,\Delta X\Delta Z e.$$
--
--   Here $X, Z, \bar X, \bar Z, \Delta X, \Delta Z$ are the diagonal matrices of the corresponding vectors and $e$ is the vector of ones, so $\Delta X\Delta Ze$ is the vector with components $\Delta x_j\Delta z_j$. These identities drive the whole convergence analysis: infeasibility and noncomplementarity are reduced by the same factor, and the deviation from centrality changes by a controlled quadratic term.
--
--   **Formalization Note** No positivity of $x$ or $z$ is assumed; the book's proof does not use it. The step length $\theta$ is an arbitrary real number.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 326, Theorem 22.2 (PDF p. 332), with Eqs. (22.5)–(22.6)

import Mathlib
import Definitions.Def_VanderbeiLP_SelfDual_HomogeneousSelfDual

open Matrix

namespace VanderbeiLP.SelfDual

/-- Theorem 22.2 (Vanderbei, p. 326). Let `A` be skew symmetric (`n ≥ 2`), `0 ≤ δ ≤ 1`, let
`(Δx, Δz)` solve (22.5)–(22.6) at `(x, z)`, let `θ` be a step length, and put
`x̄ = x + θΔx`, `z̄ = z + θΔz`. Then
(1) `Δzᵀ Δx = 0`;
(2) `ρ̄ = (1 - θ + θδ) ρ`;
(3) `μ̄ = (1 - θ + θδ) μ`;
(4) `X̄Z̄e - μ̄e = (1 - θ)(XZe - μe) + θ² ΔXΔZe`. -/
theorem step_direction_relations {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsSkewSymmetric A)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (x z dx dz : Fin n → ℝ) (hstep : IsStepDirection A δ x z dx dz) (θ : ℝ) :
    dz ⬝ᵥ dx = 0 ∧
    rho A (x + θ • dx) (z + θ • dz) = (1 - θ + θ * δ) • rho A x z ∧
    mu (x + θ • dx) (z + θ • dz) = (1 - θ + θ * δ) * mu x z ∧
    centralityResidual (x + θ • dx) (z + θ • dz) =
      (1 - θ) • centralityResidual x z + θ ^ 2 • (fun j => dx j * dz j) := by sorry

end VanderbeiLP.SelfDual

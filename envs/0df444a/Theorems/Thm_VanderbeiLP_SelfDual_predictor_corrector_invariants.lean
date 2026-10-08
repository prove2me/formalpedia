-- Prove2me | Theorems.Thm_VanderbeiLP_SelfDual_predictor_corrector_invariants
-- name    : VanderbeiLP.SelfDual.predictor_corrector_invariants
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T13:53:39.586053+00:00
-- url     : https://prove2.me/theorems/24683b42-bd7c-4c14-a18f-31e9fd428744
-- title:
--   Theorem 22.3 — the predictor step lands in $\mathcal N(1/2)$, the corrector step in $\mathcal N(1/4)$
-- statement:
--   Let $n \ge 2$ and let $A$ be a real skew-symmetric $n \times n$ matrix. Write $\mu = \mu(x, z)$, $\bar\mu = \mu(\bar x, \bar z)$.
--
--   1. **Predictor step.** Suppose $(x, z) \in \mathcal N(1/4)$, $(\Delta x, \Delta z)$ solves (22.5)–(22.6) with $\delta = 0$, and $\theta$ is the step length (22.10)
--   $$\theta = \max\{t : (x + t\Delta x, z + t\Delta z) \in \mathcal N(1/2)\}.$$
--   Then $(\bar x, \bar z) = (x + \theta\Delta x, z + \theta\Delta z) \in \mathcal N(1/2)$ and $\bar\mu = (1 - \theta)\mu$.
--   2. **Corrector step.** Suppose $(x, z) \in \mathcal N(1/2)$, $(\Delta x, \Delta z)$ solves (22.5)–(22.6) with $\delta = 1$, and $\theta = 1$. Then $(\bar x, \bar z) = (x + \Delta x, z + \Delta z) \in \mathcal N(1/4)$ and $\bar\mu = \mu$.
--
--   So each step leaves the iterate where the next step expects it, $\mu$ decreases on predictor steps and stays the same on corrector steps: the predictor–corrector algorithm is well defined.
--
--   **Formalization Note** In part (1), "$\theta$ is the maximum" is the hypothesis that $\theta$ is the greatest element of the set $\{t \in \mathbb{R} : (x + t\Delta x, z + t\Delta z) \in \mathcal N(1/2)\}$. The maximum need not exist (the supremum can be $1$ and not attained); part (1) is stated for the case where it does, as the book's (22.10) presumes.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 328, Theorem 22.3 (PDF p. 334), with the algorithm's description and Eq. (22.10) on pp. 327–328 (PDF pp. 333–334)

import Mathlib
import Definitions.Def_VanderbeiLP_SelfDual_HomogeneousSelfDual

open Matrix

namespace VanderbeiLP.SelfDual

/-- Theorem 22.3 (Vanderbei, p. 328). Let `A` be skew symmetric (`n ≥ 2`).
(1) After a predictor step — `(x, z) ∈ N(1/4)`, `(Δx, Δz)` solves (22.5)–(22.6) with
`δ = 0`, and `θ` is the maximum (22.10) of `{t : (x + tΔx, z + tΔz) ∈ N(1/2)}` — the new point
`(x̄, z̄) = (x + θΔx, z + θΔz)` lies in `N(1/2)` and `μ̄ = (1 - θ)μ`.
(2) After a corrector step — `(x, z) ∈ N(1/2)`, `(Δx, Δz)` solves (22.5)–(22.6) with `δ = 1`,
and `θ = 1` — the new point `(x̄, z̄) = (x + Δx, z + Δz)` lies in `N(1/4)` and `μ̄ = μ`. -/
theorem predictor_corrector_invariants {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsSkewSymmetric A) (x z dx dz : Fin n → ℝ) :
    ((x, z) ∈ Nbhd (1 / 4 : ℝ) → IsStepDirection A 0 x z dx dz →
      ∀ θ : ℝ, IsGreatest {t : ℝ | (x + t • dx, z + t • dz) ∈ Nbhd (1 / 2 : ℝ)} θ →
        (x + θ • dx, z + θ • dz) ∈ Nbhd (1 / 2 : ℝ) ∧
          mu (x + θ • dx) (z + θ • dz) = (1 - θ) * mu x z) ∧
    ((x, z) ∈ Nbhd (1 / 2 : ℝ) → IsStepDirection A 1 x z dx dz →
      (x + dx, z + dz) ∈ Nbhd (1 / 4 : ℝ) ∧ mu (x + dx) (z + dz) = mu x z) := by sorry

end VanderbeiLP.SelfDual

-- Prove2me | Theorems.Thm_VanderbeiLP_SelfDual_predictor_step_length_lower_bound
-- name    : VanderbeiLP.SelfDual.predictor_step_length_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T13:53:56.007157+00:00
-- url     : https://prove2.me/theorems/963f154e-ffe8-47b2-b43b-1563f5e54206
-- title:
--   Theorem 22.5 — each predictor step has length $\theta \ge 1/(2\sqrt n)$
-- statement:
--   Let $n \ge 2$ and let $A$ be a real skew-symmetric $n \times n$ matrix. Consider a predictor step of the homogeneous self-dual predictor–corrector algorithm: $(x, z) \in \mathcal N(1/4)$, and $(\Delta x, \Delta z)$ is a solution of the step equations (22.5)–(22.6) with $\delta = 0$,
--
--   $$A\Delta x + \Delta z = -\rho(x, z), \qquad Z\Delta x + X\Delta z = -XZe.$$
--
--   Then
--
--   1. for every $t$ with $0 \le t \le \frac{1}{2\sqrt n}$, the point $(x + t\Delta x, z + t\Delta z)$ lies in $\mathcal N(1/2)$; and
--   2. the predictor step length (22.10), $\theta = \sup\{t : (x + t\Delta x, z + t\Delta z) \in \mathcal N(1/2)\}$, satisfies
--   $$\theta \ge \frac{1}{2\sqrt n}.$$
--
--   Together with Theorem 22.3, this gives $\mu^{(2k)} \le \big(1 - \frac{1}{2\sqrt n}\big)^k$ along the algorithm started at $x^{(0)} = z^{(0)} = e$, hence at most $4L\sqrt n$ iterations to bring $\mu$ below $2^{-L}$ (§2.4): a complete, polynomial convergence analysis.
--
--   **Formalization Note** The book writes $\theta$ as a maximum (22.10); the maximum need not be attained, so $\theta$ is the supremum of the admissible step lengths. That set contains $0$ and is bounded above by $1$ along such a direction, so the supremum is a genuine one (no default value is involved). Part (1) is what the book's proof establishes ("since $t$ was an arbitrary number less than $(2\sqrt n)^{-1}$"); it is stated as well so that the result does not depend on how (22.10) is read. $\|\cdot\|$ in $\mathcal N(\beta)$ is the Euclidean norm.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 330, Theorem 22.5 (PDF p. 336); predictor step and Eq. (22.10) on pp. 327–328 (PDF pp. 333–334)

import Mathlib
import Definitions.Def_VanderbeiLP_SelfDual_HomogeneousSelfDual

open Matrix

namespace VanderbeiLP.SelfDual

/-- Theorem 22.5 (Vanderbei, p. 330). In each predictor step, `θ ≥ 1/(2√n)`.
Precisely: let `A` be skew symmetric (`n ≥ 2`), `(x, z) ∈ N(1/4)`, and let `(Δx, Δz)` solve
(22.5)–(22.6) with `δ = 0`. Then every step `t` with `0 ≤ t ≤ 1/(2√n)` keeps
`(x + tΔx, z + tΔz)` in `N(1/2)`, and the predictor step length (22.10)
`θ = sup{t : (x + tΔx, z + tΔz) ∈ N(1/2)}` satisfies `θ ≥ 1/(2√n)`. -/
theorem predictor_step_length_lower_bound {n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsSkewSymmetric A)
    (x z dx dz : Fin n → ℝ) (hN : (x, z) ∈ Nbhd (1 / 4 : ℝ))
    (hstep : IsStepDirection A 0 x z dx dz) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 / (2 * Real.sqrt n) →
      (x + t • dx, z + t • dz) ∈ Nbhd (1 / 2 : ℝ)) ∧
    1 / (2 * Real.sqrt n) ≤ predictorStepLength x z dx dz := by sorry

end VanderbeiLP.SelfDual

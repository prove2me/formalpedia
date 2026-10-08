-- Prove2me | Theorems.Thm_VanderbeiLP_PathFollowing_complementarity_one_step
-- name    : VanderbeiLP.PathFollowing.complementarity_one_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T19:55:46.454004+00:00
-- url     : https://prove2.me/theorems/5c19a469-c8c3-4610-9c11-ae7734488256
-- title:
--   Eq. (18.10) — $\tilde\gamma \le (1-(1-\delta)\theta)\gamma + M\|\rho\|_1 + M\|\sigma\|_1$
-- statement:
--   Let $0 < \delta < 1$ and $0 < r < 1$. Suppose $(\tilde x, \tilde w, \tilde y, \tilde z)$ is obtained from $(x, w, y, z) > 0$ by one iteration of the path-following method (Fig. 18.1 with parameter $\delta$ in $\mu = \delta\gamma/(n+m)$ and step length (18.7) with parameter $r$), with step length $\theta$. Let $\rho = b - Ax - w$, $\sigma = c - A^Ty + z$, $\gamma = z^Tx + y^Tw$ at the current point and $\tilde\gamma = \tilde z^T\tilde x + \tilde y^T\tilde w$ at the new one. If $M$ is a real number with $\|x\|_\infty \le M$ and $\|y\|_\infty \le M$, then
--
--   $$\tilde\gamma \le (1 - (1 - \delta)\theta)\gamma + M\|\rho\|_1 + M\|\sigma\|_1.$$
--
--   This is the one-step estimate for the complementarity. Unlike the infeasibilities, $\gamma$ need not decrease by a fixed factor, because the Newton step linearizes the complementarity equations; the error is controlled by the infeasibilities weighted by the size of the iterate.
--
--   **Formalization Note** The book phrases the hypothesis as a bound on $\|x\|_\infty$ and $\|y\|_\infty$ "along the sequence of points visited by the algorithm"; the estimate for one step uses the bound at the current point only, which is what is assumed here.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 277, Eq. (18.10) (PDF p. 287); derivation pp. 275–277 (PDF pp. 285–287)

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod

open Matrix

namespace VanderbeiLP.PathFollowing

/-- Vanderbei, p. 277, Eq. (18.10): if the current `x` and `y` satisfy `‖x‖∞ ≤ M` and
`‖y‖∞ ≤ M`, one step of the path-following method with step length `θ` (18.7) gives
`γ̃ ≤ (1 − (1 − δ)θ)γ + M‖ρ‖₁ + M‖σ‖₁`. -/
theorem complementarity_one_step {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (δ r : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r)
    (hr1 : r < 1) (p d p' : PDPoint m n) (hstep : IsPathFollowingStep A b c δ r p d p')
    (M : ℝ) (hx : normInf p.x ≤ M) (hy : normInf p.y ≤ M) :
    complementarity p' ≤
      (1 - (1 - δ) * stepLength r p d) * complementarity p
        + M * norm1 (primalInfeas A b p) + M * norm1 (dualInfeas A c p) := by sorry

end VanderbeiLP.PathFollowing

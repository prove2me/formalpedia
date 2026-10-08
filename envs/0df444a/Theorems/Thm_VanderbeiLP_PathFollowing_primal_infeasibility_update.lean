-- Prove2me | Theorems.Thm_VanderbeiLP_PathFollowing_primal_infeasibility_update
-- name    : VanderbeiLP.PathFollowing.primal_infeasibility_update
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T19:49:16.320992+00:00
-- url     : https://prove2.me/theorems/eb83b04a-ada7-4752-a6fb-5cf6f34e4fa8
-- title:
--   Eq. (18.8) — one step multiplies the primal infeasibility by $1 - \theta$
-- statement:
--   Let $0 < \delta < 1$ and $0 < r < 1$. Suppose $(\tilde x, \tilde w, \tilde y, \tilde z)$ is obtained from $(x, w, y, z) > 0$ by one iteration of the path-following method (Fig. 18.1 with step length (18.7)) with step length $\theta$. Write $\rho = b - Ax - w$ and $\tilde\rho = b - A\tilde x - \tilde w$ for the primal infeasibilities before and after the step. Then
--
--   $$\tilde\rho = (1 - \theta)\rho.$$
--
--   Together with $\theta \in (0, 1]$ this says that each iteration reduces the primal infeasibility, and by the factor $1 - \theta$ exactly. It gives the first conclusion of Theorem 18.1.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 275, Eq. (18.8) (PDF p. 285)

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod

open Matrix

namespace VanderbeiLP.PathFollowing

/-- Vanderbei, p. 275, Eq. (18.8): one step of the path-following method multiplies the
primal infeasibility by `1 − θ`: `ρ̃ = (1 − θ) ρ`. -/
theorem primal_infeasibility_update {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (δ r : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r)
    (hr1 : r < 1) (p d p' : PDPoint m n) (hstep : IsPathFollowingStep A b c δ r p d p') :
    primalInfeas A b p' = (1 - stepLength r p d) • primalInfeas A b p := by sorry

end VanderbeiLP.PathFollowing

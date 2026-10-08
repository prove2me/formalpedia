-- Prove2me | Theorems.Thm_VanderbeiLP_PathFollowing_dual_infeasibility_update
-- name    : VanderbeiLP.PathFollowing.dual_infeasibility_update
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T19:52:56.530285+00:00
-- url     : https://prove2.me/theorems/c4b96306-6f5b-4a51-8578-17150d57336f
-- title:
--   Eq. (18.9) — one step multiplies the dual infeasibility by $1 - \theta$
-- statement:
--   Let $0 < \delta < 1$ and $0 < r < 1$. Suppose $(\tilde x, \tilde w, \tilde y, \tilde z)$ is obtained from $(x, w, y, z) > 0$ by one iteration of the path-following method (Fig. 18.1 with step length (18.7)) with step length $\theta$. Write $\sigma = c - A^Ty + z$ and $\tilde\sigma = c - A^T\tilde y + \tilde z$ for the dual infeasibilities before and after the step. Then
--
--   $$\tilde\sigma = (1 - \theta)\sigma.$$
--
--   This is the dual counterpart of Eq. (18.8) and gives the second conclusion of Theorem 18.1.
--
--   **Formalization Note** The book's middle expression prints $\theta(A\Delta y - \Delta z)$; by (18.2) the intended term is $\theta(A^T\Delta y - \Delta z)$. Only the final identity $\tilde\sigma = (1-\theta)\sigma$ is stated.
-- source:
--   Vanderbei, Linear Programming: Foundations and Extensions, 4th ed., Springer 2014, p. 275, Eq. (18.9) (PDF p. 285)

import Mathlib
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod

open Matrix

namespace VanderbeiLP.PathFollowing

/-- Vanderbei, p. 275, Eq. (18.9): one step of the path-following method multiplies the
dual infeasibility by `1 − θ`: `σ̃ = (1 − θ) σ`. -/
theorem dual_infeasibility_update {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (δ r : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr0 : 0 < r)
    (hr1 : r < 1) (p d p' : PDPoint m n) (hstep : IsPathFollowingStep A b c δ r p d p') :
    dualInfeas A c p' = (1 - stepLength r p d) • dualInfeas A c p := by sorry

end VanderbeiLP.PathFollowing

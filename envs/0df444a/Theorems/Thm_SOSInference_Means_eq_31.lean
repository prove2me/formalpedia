-- Prove2me | Theorems.Thm_SOSInference_Means_eq_31
-- name    : SOSInference.Means.eq_31
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:39.756063+00:00
-- url     : https://prove2.me/theorems/7357373c-1af5-4ebb-9645-a771e9230d4e
-- title:
--   (31) — the fixed-point equation $1/\rho=\tilde g(\rho\tilde Z)$ has a unique solution
-- statement:
--   Assume A1)–A4) with $l=2$. For every $z\in\mathbb R^2$ with $z\ne0$, the equation
--   $$\frac1\rho=\tilde g(\rho z),\qquad \tilde g(x)=\mathbb P\big(\tau(0)\le\|x\|_2^2\big),$$
--   has exactly one solution $\rho>0$. Consequently $\rho(z)$, defined as this solution, is positive and satisfies $1/\rho(z)=\tilde g(\rho(z)z)$.
--
--   The solution $\rho(\tilde Z)$ is the scale of the maximiser $\zeta^*=-\rho(\tilde Z)\tilde Z$ of the limiting dual objective in dimension two, and enters the $l=2$ limit law of Theorem 1.
--
--   **Formalization Note** The restriction $z\ne0$ is needed: at $z=0$ the equation reads $1/\rho=\tilde g(0)=0$ and has no solution.
-- source:
--   Blanchet, Kang, Sample Out-of-Sample Inference Based on Wasserstein Distance, arXiv:1605.01340v4, p. 45, §7.2.5, (31)

import Mathlib
import Definitions.Def_SOSInference_Means_tauLaw

namespace SOSInference.Means

/-- **(31)**, §7.2.5, p. 45 (Blanchet, Kang, Sample Out-of-Sample Inference Based on Wasserstein
Distance, arXiv:1605.01340v4, p. 45, (31)): for `l = 2`, under A1)–A4), for every `z ≠ 0` the
equation `1/ρ = g̃(ρz)` has a unique solution `ρ > 0`; consequently `ρ(z)` (defined as that
solution) satisfies it.

**Formalization Note.** `z ≠ 0` is needed: at `z = 0` the equation reads `1/ρ = g̃(0) = 0` and has
no solution (`ρ(0) := 0` by convention). -/
theorem eq_31 (M : Model 2) (hM : M.Standing) (z : E 2) (hz : z ≠ 0) :
    (∃! r : ℝ, 0 < r ∧ 1 / r = gtilde M (r • z)) ∧
      0 < rho M z ∧ 1 / rho M z = gtilde M (rho M z • z) := by sorry

end SOSInference.Means

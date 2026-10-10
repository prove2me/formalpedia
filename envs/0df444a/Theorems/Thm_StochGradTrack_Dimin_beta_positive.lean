-- Prove2me | Theorems.Thm_StochGradTrack_Dimin_beta_positive
-- name    : StochGradTrack.Dimin.beta_positive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:48:39.536617+00:00
-- url     : https://prove2.me/theorems/e887604a-25b5-43f4-bffb-327685e6ba2d
-- title:
--   (31), p. 425 — β₀ > 0 iff m > (4θLρ_w² + 2θLρ_w√(1+3ρ_w²))/(1−ρ_w²), and then β_k > 0 for all k
-- statement:
--   Let $\theta,L,m>0$ and $0<\rho<1$, and set
--   $$\beta_0=\frac{1-\rho^2}{2\rho^2}-\frac{4\theta L}{m}-\frac{2\theta^2L^2}{m^2}.$$
--   Then
--   $$\beta_0>0\iff m>\frac{4\theta L\rho^2+2\theta L\rho\sqrt{1+3\rho^2}}{1-\rho^2},$$
--   and if $\beta_0>0$ then $\beta_k=\frac{1-\rho^2}{2\rho^2}-4\alpha_kL-2\alpha_k^2L^2>0$ for every $k\ge0$, where $\alpha_k=\theta/(m+k)$.
--
--   This turns the requirement $\beta_k>0$ of the linear system (29) into the first condition (14) on $m$.
--
--   **Formalization Note** In the theorems $\rho=\rho_w$; here $\rho$ is a free real number with $0<\rho<1$, which is what Lemma 1 gives for $\rho_w$ together with the standing addition $\rho_w>0$.
-- source:
--   Pu & Nedić, Math. Program. 187 (2021), §3.3, β₀ and (31), p. 425

import Mathlib
import Definitions.Def_StochGradTrack_Dimin_StepSystem

namespace StochGradTrack.Dimin

/-- (31) (p. 425): for `0 < ρ < 1`, `β₀ > 0` is equivalent to the lower bound (31) on `m`, and it implies
`β_k > 0` for every `k`. -/
theorem beta_positive (θ L m ρ : ℝ) (hθ : 0 < θ) (hL : 0 < L) (hm : 0 < m) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (0 < (1 - ρ ^ 2) / (2 * ρ ^ 2) - 4 * θ * L / m - 2 * θ ^ 2 * L ^ 2 / m ^ 2 ↔
      (4 * θ * L * ρ ^ 2 + 2 * θ * L * ρ * Real.sqrt (1 + 3 * ρ ^ 2)) / (1 - ρ ^ 2) < m) ∧
    (0 < (1 - ρ ^ 2) / (2 * ρ ^ 2) - 4 * θ * L / m - 2 * θ ^ 2 * L ^ 2 / m ^ 2 →
      ∀ k : ℕ, 0 < betaK θ m L ρ k) := by sorry

end StochGradTrack.Dimin

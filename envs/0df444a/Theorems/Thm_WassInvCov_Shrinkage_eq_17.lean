-- Prove2me | Theorems.Thm_WassInvCov_Shrinkage_eq_17
-- name    : WassInvCov.Shrinkage.eq_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:34.756269+00:00
-- url     : https://prove2.me/theorems/95d71d41-4d45-4795-b6b3-4edc3d499ab3
-- title:
--   Identity (17), p. 12 — (γ⋆)² x⋆_i λ_i = (γ⋆ − x⋆_i)²
-- statement:
--   Let $\rho>0$, $\lambda_1,\dots,\lambda_p\ge0$, and let $\gamma^\star>0$ solve (16b). With $x^\star_i=\gamma^\star\big[1-\frac12\big(\sqrt{\lambda_i^2(\gamma^\star)^2+4\lambda_i\gamma^\star}-\lambda_i\gamma^\star\big)\big]$ as in (16a),
--
--   $$(\gamma^\star)^2x^\star_i\lambda_i=(\gamma^\star-x^\star_i)^2\qquad\text{for all }i\le p.\tag{17}$$
--
--   The identity is what makes the gradient of the objective of (6) with respect to $X$ vanish at $(X^\star,\gamma^\star)$ in the proof of Theorem 3.1.
--
--   **Formalization Note** The hypotheses are those of the page. The identity in fact holds for every $\gamma\ge0$ in place of $\gamma^\star$, by algebra alone; the root hypothesis is kept as on the page.
-- source:
--   Nguyen, Kuhn & Mohajerin Esfahani, Distributionally Robust Inverse Covariance Estimation, arXiv:1805.07194v1, p. 12, proof of Theorem 3.1, (17)

import Mathlib
import Definitions.Def_WassInvCov_Shrinkage_Setting

open MeasureTheory ProbabilityTheory Matrix

namespace WassInvCov.Shrinkage

/-- Identity (17), p. 12 (arXiv:1805.07194v1): at the positive root `γ⋆` of (16b), the values
`x⋆ᵢ` of (16a) satisfy `(γ⋆)² x⋆ᵢ λᵢ = (γ⋆ − x⋆ᵢ)²` for every `i`. -/
theorem eq_17 {p : ℕ} (ρ : ℝ) (hρ : 0 < ρ) (lam : Fin p → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (γs : ℝ) (hγs : 0 < γs) (hroot : phi16b ρ lam γs = 0) :
    ∀ i, γs ^ 2 * x16a lam γs i * lam i = (γs - x16a lam γs i) ^ 2 := by sorry

end WassInvCov.Shrinkage

-- Prove2me | Theorems.Thm_WassInvCov_Shrinkage_rho_sq_gamma_sq_eq_sum
-- name    : WassInvCov.Shrinkage.rho_sq_gamma_sq_eq_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:30:39.677689+00:00
-- url     : https://prove2.me/theorems/6e744b71-8e16-4300-900e-0feb09a4365a
-- title:
--   Proof of Theorem 3.1, p. 13 — at the positive root of (16b), ρ²(γ⋆)² = Σ_i x⋆_i
-- statement:
--   Let $\rho>0$, $\lambda_1,\dots,\lambda_p\ge0$, let $\gamma^\star>0$ solve (16b), and let $x^\star_1,\dots,x^\star_p$ be given by (16a) at $\gamma^\star$. Then
--
--   $$\rho^2(\gamma^\star)^2=\sum_{i=1}^p x^\star_i.$$
--
--   This observation makes the partial derivative of the objective of (6) with respect to $\gamma$ vanish at $(X^\star,\gamma^\star)$ in the proof of Theorem 3.1.
-- source:
--   Nguyen, Kuhn & Mohajerin Esfahani, Distributionally Robust Inverse Covariance Estimation, arXiv:1805.07194v1, p. 13, proof of Theorem 3.1, last equality of the display for ∂f/∂γ

import Mathlib
import Definitions.Def_WassInvCov_Shrinkage_Setting

open MeasureTheory ProbabilityTheory Matrix

namespace WassInvCov.Shrinkage

/-- Proof of Theorem 3.1, p. 13 (arXiv:1805.07194v1): at the positive root `γ⋆` of (16b), the values
`x⋆ᵢ` of (16a) satisfy `ρ² (γ⋆)² = Σᵢ x⋆ᵢ`. -/
theorem rho_sq_gamma_sq_eq_sum {p : ℕ} (ρ : ℝ) (hρ : 0 < ρ) (lam : Fin p → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (γs : ℝ) (hγs : 0 < γs) (hroot : phi16b ρ lam γs = 0) :
    ρ ^ 2 * γs ^ 2 = ∑ i, x16a lam γs i := by sorry

end WassInvCov.Shrinkage

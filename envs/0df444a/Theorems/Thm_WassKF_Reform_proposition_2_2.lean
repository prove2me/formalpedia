-- Prove2me | Theorems.Thm_WassKF_Reform_proposition_2_2
-- name    : WassKF.Reform.proposition_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:09:04.743983+00:00
-- url     : https://prove2.me/theorems/7d2f0187-1d62-4946-98a3-e5917a730ff2
-- title:
--   Proposition 2.2 — $W_2(\mathcal N_d(\mu_1,\Sigma_1),\mathcal N_d(\mu_2,\Sigma_2))$ equals the Gelbrich formula
-- statement:
--   Let $\mu_1, \mu_2 \in \mathbb R^d$ and let $\Sigma_1, \Sigma_2 \in \mathbb S^d_+$ be positive semidefinite. The type-2 Wasserstein distance between the normal distributions $\mathbb Q_1 = \mathcal N_d(\mu_1, \Sigma_1)$ and $\mathbb Q_2 = \mathcal N_d(\mu_2, \Sigma_2)$ is
--
--   $$
--   W_2(\mathbb Q_1, \mathbb Q_2) = \sqrt{\|\mu_1 - \mu_2\|^2 + \operatorname{Tr}\Bigl[\Sigma_1 + \Sigma_2 - 2\bigl(\Sigma_2^{1/2} \Sigma_1 \Sigma_2^{1/2}\bigr)^{1/2}\Bigr]},
--   $$
--
--   where $A^{1/2}$ is the positive semidefinite square root of $A \succeq 0$.
--
--   The formula turns the constraint $W_2(\mathbb Q, \mathbb P) \le \rho$ defining the ambiguity set (3) into an explicit constraint on the mean and covariance of $\mathbb Q$; it is used this way in the proofs of Theorems 2.3 and 2.5.
--
--   **Formalization Note** The space is `EuclideanSpace ℝ (Fin n ⊕ Fin m)` with $d = n + m$, the space on which the published coupling-based `wassersteinDistance` is defined. Both sides are in $[0,\infty]$, the right side as `ENNReal.ofReal (Real.sqrt …)`. The square root is the published `psdSqrt`, and the page's order $\Sigma_2^{1/2}\Sigma_1\Sigma_2^{1/2}$ is kept.
-- source:
--   Shafieezadeh-Abadeh, Nguyen, Kuhn, Mohajerin Esfahani, Wasserstein Distributionally Robust Kalman Filtering, arXiv:1809.08830v3, p. 3, Proposition 2.2 (cited from Gelbrich 1990, Proposition 7)

import Mathlib
import Definitions.Def_WassersteinDRO_Shrinkage_wassersteinDistance
import Definitions.Def_WassersteinDRO_Shrinkage_psdSqrt

open MeasureTheory ProbabilityTheory

namespace WassKF.Reform

/-- Proposition 2.2 (Gelbrich formula for normal distributions, cited from [12, Proposition 7]),
Shafieezadeh-Abadeh et al., arXiv:1809.08830v3, p. 3. For `Q₁ = 𝒩_d(μ₁, S₁)` and
`Q₂ = 𝒩_d(μ₂, S₂)` with `S₁, S₂ ⪰ 0`,
`W₂(Q₁, Q₂) = √(‖μ₁ − μ₂‖² + Tr[S₁ + S₂ − 2 (S₂^{1/2} S₁ S₂^{1/2})^{1/2}])`.
`ℝ^d` is `EuclideanSpace ℝ (Fin n ⊕ Fin m)`, the space on which the reused coupling-based
`wassersteinDistance` is defined. -/
theorem proposition_2_2 {n m : ℕ} (μ₁ μ₂ : EuclideanSpace ℝ (Fin n ⊕ Fin m))
    (S₁ S₂ : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ)
    (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef) :
    WassersteinDRO.Shrinkage.wassersteinDistance 2
        (multivariateGaussian μ₁ S₁) (multivariateGaussian μ₂ S₂) =
      ENNReal.ofReal (Real.sqrt (‖μ₁ - μ₂‖ ^ 2 +
        (S₁ + S₂ - (2 : ℝ) • WassersteinDRO.Shrinkage.psdSqrt
          (WassersteinDRO.Shrinkage.psdSqrt S₂ * S₁ * WassersteinDRO.Shrinkage.psdSqrt S₂)).trace)) := by sorry

end WassKF.Reform

-- Prove2me | Theorems.Thm_WassersteinDRO_Gelbrich_projection_ambiguity_set
-- name    : WassersteinDRO.Gelbrich.projection_ambiguity_set
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T02:28:12.621293+00:00
-- url     : https://prove2.me/theorems/a0c00f9b-e37e-4cc7-8078-068f45341b24
-- title:
--   Proposition 1 — Projection of the Wasserstein ball onto the mean-covariance space
-- statement:
--   If $\hat P_N$ has mean vector $\hat\mu$ and covariance matrix $\hat\Sigma$, the image of the
--   type-2 Wasserstein ambiguity set $B_{\varepsilon,2}(\hat P_N)$ under $Q \mapsto (E_Q[\xi],
--   \mathrm{Cov}_Q[\xi])$ is contained in $U_\varepsilon(\hat\mu,\hat\Sigma)$; the inclusion becomes
--   an equality when $\Xi = \mathbb{R}^m$ and $\hat P_N = E_g(\hat\mu,\hat\Sigma)$ is an elliptical
--   distribution.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, Proposition 1, p. 16-17

import Mathlib
import Definitions.Def_WassersteinDRO_Gelbrich_ambiguitySet
import Definitions.Def_WassersteinDRO_Gelbrich_meanVector
import Definitions.Def_WassersteinDRO_Gelbrich_covarianceMatrix
import Definitions.Def_WassersteinDRO_Gelbrich_meanCovarianceUncertaintySet
import Definitions.Def_WassersteinDRO_Gelbrich_IsElliptical

open MeasureTheory

namespace WassersteinDRO.Gelbrich

/-- Proposition 1 (Projection of `B_{ε,2}(P̂N)` onto the mean-covariance space), Kuhn et al.
2019, p. 16-17: if `P̂N` has mean vector `μ̂` and covariance matrix `Ŝ`, then the image of the
Wasserstein ambiguity set under `Q ↦ (E_Q[ξ], Cov_Q[ξ])` is contained in `U_ε(μ̂,Ŝ)`; the
inclusion becomes an equality if `Ξ = R^m` and `P̂N` is an elliptical distribution
`E_g(μ̂,Ŝ)`. -/
theorem projection_ambiguity_set {m : ℕ} (ε : ℝ) (Ξ : Set (EuclideanSpace ℝ (Fin m)))
    (PN : Measure (EuclideanSpace ℝ (Fin m))) (μhat : EuclideanSpace ℝ (Fin m))
    (SigmaHat : Matrix (Fin m) (Fin m) ℝ)
    (hμ : meanVector PN = μhat) (hS : covarianceMatrix PN = SigmaHat) :
    (∀ Q ∈ ambiguitySet ε 2 Ξ PN,
        (meanVector Q, covarianceMatrix Q) ∈ meanCovarianceUncertaintySet ε μhat SigmaHat) ∧
    (Ξ = Set.univ → (∃ g : ℝ → ℝ, IsElliptical PN g μhat SigmaHat) →
      ∀ pair ∈ meanCovarianceUncertaintySet ε μhat SigmaHat,
        ∃ Q ∈ ambiguitySet ε 2 Ξ PN, (meanVector Q, covarianceMatrix Q) = pair) := by sorry

end WassersteinDRO.Gelbrich

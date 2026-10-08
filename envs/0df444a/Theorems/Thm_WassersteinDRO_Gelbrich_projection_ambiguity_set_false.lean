-- Prove2me | Theorems.Thm_WassersteinDRO_Gelbrich_projection_ambiguity_set_false
-- name    : WassersteinDRO.Gelbrich.projection_ambiguity_set_false
-- status  : Open
-- author  : @junyihjy
-- created : 2026-10-06T07:27:13.890854+00:00
-- url     : https://prove2.me/theorems/fe3298c3-c439-469c-a4ba-cd7e4efa4022
-- title:
--   Negation of the Gelbrich projection (false as formalized)
-- statement:
--   Negation of WassersteinDRO.Gelbrich.projection_ambiguity_set (a0c00f9b), which is false as formalized.
--
--   The formalized Proposition 1 claims the image of the type-2 Wasserstein ambiguity set under Q -> (meanVector Q, covarianceMatrix Q) is contained in the mean-covariance uncertainty set U_e(muhat, SigmaHat). But the nominal PN is not assumed to have finite second moments, and covarianceMatrix is a Bochner integral (junk value 0 on non-integrable entries), so it can be non-positive-semidefinite — which meanCovarianceUncertaintySet explicitly forbids via a PosSemidef conjunct.
--
--   Counterexample: m = 2, Xi = univ, eps = 1, muhat = 0, PN = law of (sign X, X) for symmetric X with density proportional to 1/(1+|x|^3) (so E|X| < inf = E[X^2]). Then meanVector PN = (0,0) and covarianceMatrix PN = !![1, c; c, 0] with c = E|X| > 0, det = -c^2 < 0, hence not PSD. PN is in ambiguitySet (diagonal coupling gives W_2(PN,PN) = 0 <= 1) but (meanVector PN, covarianceMatrix PN) is rejected by the PosSemidef conjunct of U. The first conjunct fails at Q = PN. The paper's Proposition 1 assumes finite second moments; the formalization does not.
-- source:
--   Kuhn, Esfahani, Nguyen, Shafieezadeh-Abadeh, 'Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning', 2019, Proposition 1 p. 16-17. Falsity finding: the formalization drops the finite-second-moments hypothesis on the nominal distribution; the Bochner covariance can then be non-PSD (junk value 0 on non-integrable entries), contradicting the PosSemidef conjunct of meanCovarianceUncertaintySet. Counterexample: PN = law of (sign X, X), X symmetric with E|X|<inf=E[X^2]; first conjunct fails at Q = PN.

import Mathlib
import Definitions.Def_WassersteinDRO_Gelbrich_ambiguitySet
import Definitions.Def_WassersteinDRO_Gelbrich_meanVector
import Definitions.Def_WassersteinDRO_Gelbrich_covarianceMatrix
import Definitions.Def_WassersteinDRO_Gelbrich_meanCovarianceUncertaintySet
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace WassersteinDRO.Gelbrich

/-- Proposition 1 (Projection of `B_{ε,2}(P̂N)` onto the mean-covariance space),
Kuhn et al. 2019, p. 16-17, is FALSE as formalized: the nominal distribution
`P̂N` is not assumed to have finite second moments, so `covarianceMatrix PN`
(a Bochner integral, junk value `0` on non-integrable entries) can fail to be
positive semidefinite — which `meanCovarianceUncertaintySet` explicitly requires
via its `PosSemidef` conjunct. Concretely, with `m = 2`, `Ξ = univ`, `ε = 1`,
`μ̂ = 0`, the law `PN` of `(sign X, X)` for symmetric `X` with
`E|X| < ∞ = E[X²]` satisfies `PN ∈ ambiguitySet 1 2 univ PN`
(the diagonal coupling gives `W₂(PN,PN) = 0 ≤ 1`),
`(meanVector PN, covarianceMatrix PN) = (0, !![1, E|X|; E|X|, 0])`, and
`!![1, E|X|; E|X|, 0]` has negative determinant, hence is not positive
semidefinite — so the first conjunct fails at `Q = PN`. The paper's Proposition 1
assumes finite second moments; the formalization does not. -/
theorem projection_ambiguity_set_false :
    ¬∀ {m : ℕ} (ε : ℝ) (Ξ : Set (EuclideanSpace ℝ (Fin m)))
      (PN : Measure (EuclideanSpace ℝ (Fin m))) (μhat : EuclideanSpace ℝ (Fin m))
      (SigmaHat : Matrix (Fin m) (Fin m) ℝ)
      (hμ : meanVector PN = μhat) (hS : covarianceMatrix PN = SigmaHat),
      (∀ Q ∈ ambiguitySet ε 2 Ξ PN,
      (meanVector Q, covarianceMatrix Q) ∈ meanCovarianceUncertaintySet ε μhat SigmaHat):= by sorry

end WassersteinDRO.Gelbrich

-- Prove2me | Theorems.Thm_WassersteinDRO_Gelbrich_gelbrich_hull_containment_false
-- name    : WassersteinDRO.Gelbrich.gelbrich_hull_containment_false
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-05T09:54:13.905913+00:00
-- url     : https://prove2.me/theorems/a23da149-4105-4e1e-8283-c4e894ea51df
-- title:
--   Negation of the Gelbrich-hull containment (false as formalized)
-- statement:
--   Negation of WassersteinDRO.Gelbrich.gelbrich_hull_containment (d5fc0224), which is false as formalized.
--
--   The formalized containment claims that every nominal distribution PN with matching mean/covariance has its Wasserstein ambiguity set inside the Gelbrich hull. But the nominal PN is not assumed to have finite second moments, and covarianceMatrix is a Bochner integral (junk value 0 on non-integrable entries), so it can be non-positive-semidefinite — which the mean-covariance uncertainty set explicitly forbids via a PosSemidef conjunct.
--
--   Counterexample: m = 2, Ξ = univ, ε = 1, p = 2, μhat = 0, PN = law of (sign X, X) for symmetric X with density proportional to 1/(1+|x|^3) (so E|X| < ∞ < E[X²]). Then meanVector PN = (0,0) and covarianceMatrix PN = !![1, c; c, 0] with c = E|X| > 0, det = -c^2 < 0, hence not PSD. PN ∈ ambiguitySet (diagonal coupling gives W₂(PN,PN) = 0 ≤ 1) but PN ∉ gelbrichHull. The inclusion fails. The paper's Theorem 13 assumes finite second moments; the formalization does not.
-- source:
--   Kuhn, Esfahani, Nguyen, Shafieezadeh-Abadeh, 'Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning', 2019, Theorem 13 p. 18. Falsity finding: the formalization drops the finite-second-moments hypothesis on the nominal distribution; the Bochner covariance can then be non-PSD (junk value 0 on non-integrable entries), contradicting the PosSemidef conjunct of meanCovarianceUncertaintySet. Counterexample: PN = law of (sign X, X), X symmetric with E|X|<∞<E[X²].

import Mathlib
import Definitions.Def_WassersteinDRO_Gelbrich_ambiguitySet
import Definitions.Def_WassersteinDRO_Gelbrich_gelbrichHull
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal

namespace WassersteinDRO.Gelbrich

/-- The Gelbrich-hull containment (Theorem 13, Kuhn et al. 2019) is FALSE as
formalized: the nominal distribution `PN` is not assumed to have finite
second moments, so `covarianceMatrix PN` (a Bochner integral, junk value `0`
on non-integrable entries) can fail to be positive semidefinite — which the
mean-covariance uncertainty set explicitly requires. Concretely, with
`m = 2`, `Ξ = univ`, `ε = 1`, `p = 2`, `μhat = 0`, the law `PN` of
`(sign X, X)` for symmetric `X` with `E|X| < ∞ < E[X²]` satisfies
`PN ∈ ambiguitySet 1 2 univ PN` (the diagonal coupling gives
`W₂(PN,PN) = 0 ≤ 1`) but `PN ∉ gelbrichHull 1 univ 0 (covarianceMatrix PN)`
because `covarianceMatrix PN = !![1, E|X|; E|X|, 0]` has negative
determinant, hence is not positive semidefinite. So the inclusion fails. -/
theorem gelbrich_hull_containment_false :
    ¬∀ {m : ℕ} (ε p : ℝ), 2 ≤ p → (Ξ : Set (EuclideanSpace ℝ (Fin m))) →
      (PN : Measure (EuclideanSpace ℝ (Fin m))) →
      (μhat : EuclideanSpace ℝ (Fin m)) → (SigmaHat : Matrix (Fin m) (Fin m) ℝ) →
      meanVector PN = μhat → covarianceMatrix PN = SigmaHat →
      ambiguitySet ε p Ξ PN ⊆ gelbrichHull ε Ξ μhat SigmaHat := by sorry

end WassersteinDRO.Gelbrich

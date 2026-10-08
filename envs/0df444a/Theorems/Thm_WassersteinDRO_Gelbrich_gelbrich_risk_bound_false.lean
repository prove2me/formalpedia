-- Prove2me | Theorems.Thm_WassersteinDRO_Gelbrich_gelbrich_risk_bound_false
-- name    : WassersteinDRO.Gelbrich.gelbrich_risk_bound_false
-- status  : Open
-- author  : @junyihjy
-- created : 2026-10-06T08:05:03.685185+00:00
-- url     : https://prove2.me/theorems/e73ba6db-c3ef-4b0c-90c6-86b1eb0e6889
-- title:
--   Negation of the Gelbrich risk bound (false as formalized)
-- statement:
--   Negation of WassersteinDRO.Gelbrich.gelbrich_risk_bound (5a756296), which is false as formalized.
--
--   The formalized Corollary 1 claims worstCaseRisk ε p Ξ PN ℓ ≤ gelbrichRisk ε Ξ μhat SigmaHat ℓ whenever PN has mean μhat and covariance SigmaHat and p ≥ 2. But PN is not assumed to have finite second moments, and covarianceMatrix is a Bochner integral (junk value 0 on non-integrable entries), so SigmaHat can be non-positive-semidefinite — while the Gelbrich hull's mean-covariance uncertainty set explicitly requires PosSemidef.
--
--   Counterexample: m = 2, Ξ = univ, ε = 1, p = 2, μhat = 0, SigmaHat = covarianceMatrix PN for PN = law of (sign X, X), X symmetric with density proportional to 1/(1+|x|^3) (so E|X| < ∞ < E[X²]), ℓ(z) = (z 0)^2. Then covarianceMatrix PN = !![1, c; c, 0] with c = E|X| > 0, det = -c^2 < 0, not PSD. The junk psdSqrt gives psdSqrt SigmaHat = 0, and the uncertainty-set trace condition ‖μ‖² + 1 + tr Σ ≤ 1 with Σ PSD forces every hull member to (mean, cov) = (0, 0), so gelbrichRisk = 0. But PN ∈ ambiguitySet (diagonal coupling, W₂(PN,PN) = 0 ≤ 1) and nominalRisk PN ℓ = E[(sign X)²] = 1, so worstCaseRisk ≥ 1. The claimed ≤ is false (1 ≤ 0).
-- source:
--   Kuhn, Esfahani, Nguyen, Shafieezadeh-Abadeh, 'Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning', 2019, Corollary 1 p. 18 eq. (18). Falsity finding: the formalization drops the finite-second-moments hypothesis on the nominal distribution; the Bochner covariance can then be non-PSD (junk value 0 on non-integrable entries), and the junk psdSqrt collapses the Gelbrich hull while the ambiguity set retains the junk law. Counterexample: PN = law of (sign X, X), X symmetric with E|X|<∞<E[X²]; ℓ(z)=(z 0)² gives worstCaseRisk ≥ 1 > 0 = gelbrichRisk.

import Mathlib
import Definitions.Def_WassersteinDRO_Gelbrich_worstCaseRisk
import Definitions.Def_WassersteinDRO_Gelbrich_gelbrichRisk
set_option autoImplicit false
open MeasureTheory

namespace WassersteinDRO.Gelbrich

/-- Corollary 1 (Gelbrich risk), Kuhn et al. 2019, p. 18, eq. (18), is FALSE as
formalized: the nominal distribution `PN` is not assumed to have finite second
moments, so `covarianceMatrix PN` (a Bochner integral, junk value `0` on
non-integrable entries) can fail to be positive semidefinite. The junk
`psdSqrt` then collapses the Gelbrich hull to near-`{dirac 0}` while the
Wasserstein ambiguity set still contains the junk law itself. Concretely, with
`m = 2`, `Ξ = univ`, `ε = 1`, `p = 2`, `μhat = 0`,
`SigmaHat = covarianceMatrix PN` for the law `PN` of `(sign X, X)` (`X`
symmetric with `E|X| < ∞ < E[X²]`), and `ℓ(z) = (z 0)^2`: every
`Q ∈ gelbrichHull` is forced to `(meanVector Q, covarianceMatrix Q) = (0, 0)`
by the `PosSemidef` conjunct plus the trace condition
(`‖μ‖² + 1 + tr Σ ≤ 1`), so `gelbrichRisk = 0`; but `PN ∈ ambiguitySet` (the
diagonal coupling gives `W₂(PN,PN) = 0 ≤ 1`) with `nominalRisk PN ℓ = 1`, so
`worstCaseRisk ≥ 1`. Hence `worstCaseRisk ≤ gelbrichRisk` is false. -/
theorem gelbrich_risk_bound_false :
    ¬∀ {m : ℕ} (ε p : ℝ), 2 ≤ p → (Ξ : Set (EuclideanSpace ℝ (Fin m))) →
      (PN : Measure (EuclideanSpace ℝ (Fin m))) →
      (μhat : EuclideanSpace ℝ (Fin m)) → (SigmaHat : Matrix (Fin m) (Fin m) ℝ) →
      meanVector PN = μhat → covarianceMatrix PN = SigmaHat →
      (ℓ : EuclideanSpace ℝ (Fin m) → ℝ) →
      worstCaseRisk ε p Ξ PN ℓ ≤ gelbrichRisk ε Ξ μhat SigmaHat ℓ := by sorry

end WassersteinDRO.Gelbrich

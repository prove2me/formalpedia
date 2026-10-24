-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P21_maxRelative_mixture_bound
-- name    : QAlgorithms.Papers.Independent.Support50.P21.maxRelative_mixture_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:45:18.780252+00:00
-- url     : https://prove2.me/theorems/2bc5503b-b7e2-4fde-9bf3-05341e4f25d8
-- title:
--   Lemma 9
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces, and logarithms have base two.
--
--   Let $K$ be a nonempty finite set, $p_i\ge0$ with $\sum_i p_i=1$, and let $\rho_i,\sigma_i$ be density operators. Using the same weights in both mixtures,
--
--   $$D_{\max}\!\left(\sum_i p_i\rho_i\middle\Vert\sum_i p_i\sigma_i\right)\le\max_{i\in K}D_{\max}(\rho_i\Vert\sigma_i).$$
--
--   The maximum may be $+\infty$. This is the source's maximum bound, including zero-weight components.
-- source:
--   Min- and Max- Relative Entropies and a New Entanglement Monotone, arXiv:0803.2770v3, PDF p. 5, Lemma 9

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P21

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- Use the accepted declarations directly; no paper-local aliases hide dimension binders.

open QAlgorithms.Papers.Independent.Claimed50.P33
  (FiniteState IsAverageLocalMonotone IsAdaptiveLOCCMonotone)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

section Statements

variable [Nonempty I] [Nonempty J]

/-- Lemma 9, PDF p.5, (25): common weights and finite maximum, not an average. -/
theorem maxRelative_mixture_bound {K : Type} [Fintype K] [Nonempty K]
    (p : K → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (rho sigma : K → Mat I) (hrho : ∀ i, IsDensityMatrix (rho i))
    (hsigma : ∀ i, IsDensityMatrix (sigma i)) :
    maxRelative (∑ i, (p i : ℂ) • rho i) (∑ i, (p i : ℂ) • sigma i) ≤
      ⨆ i, maxRelative (rho i) (sigma i) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P21

end

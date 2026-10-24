-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P21_min_le_max
-- name    : QAlgorithms.Papers.Independent.Support50.P21.min_le_max
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:42:14.346337+00:00
-- url     : https://prove2.me/theorems/bfbfb95d-9510-4ac7-a4ff-62aea8c647a6
-- title:
--   Lemma 5
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces, and logarithms have base two.
--
--   For a density operator $\rho$ and any positive operator $\sigma$,
--
--   $$D_{\min}(\rho\Vert\sigma)\le D_{\max}(\rho\Vert\sigma).$$
--
--   The normalization of $\rho$ is essential; $\sigma$ need not have trace one. The inequality includes extended values when supports fail to overlap or include one another.
-- source:
--   Min- and Max- Relative Entropies and a New Entanglement Monotone, arXiv:0803.2770v3, PDF p. 4, Lemma 5

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

/-- Lemma 5, PDF p.4, (17): rho is NORMALIZED; sigma need only be positive. -/
theorem min_le_max (rho sigma : Mat I) (hrho : IsDensityMatrix rho)
    (hsigma : sigma.PosSemidef) : dMin rho sigma ≤ maxRelative rho sigma := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P21

end

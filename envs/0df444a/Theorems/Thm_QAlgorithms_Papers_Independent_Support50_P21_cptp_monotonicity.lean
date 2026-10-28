-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P21_cptp_monotonicity
-- name    : QAlgorithms.Papers.Independent.Support50.P21.cptp_monotonicity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T20:43:47.485859+00:00
-- url     : https://prove2.me/theorems/927f5e77-8cb5-4544-9d7b-9f7c8ca28ca4
-- title:
--   Lemma 7
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces, and logarithms have base two.
--
--   Let $\rho$ be a density operator, $\sigma\ge0$, and $T$ any completely positive trace-preserving map between finite-dimensional systems. Then
--
--   $$D_{\min}(T(\rho)\Vert T(\sigma))\le D_{\min}(\rho\Vert\sigma),\qquad D_{\max}(T(\rho)\Vert T(\sigma))\le D_{\max}(\rho\Vert\sigma).$$
--
--   The output dimension is arbitrary and $\sigma$ is not required to be normalized. This is data processing for both divergences.
-- source:
--   Min- and Max- Relative Entropies and a New Entanglement Monotone, arXiv:0803.2770v3, PDF p. 4, Lemma 7

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

/-- Lemma 7, PDF p.4, (18)–(19): arbitrary finite output dimension and Kraus CPTP.
The reversed Petz inequality inside the printed proof is not copied. -/
theorem cptp_monotonicity (rho sigma : Mat I) (hrho : IsDensityMatrix rho)
    (hsigma : sigma.PosSemidef) (T : Superop I J) (hT : IsChannel T) :
    dMin (T rho) (T sigma) ≤ dMin rho sigma ∧
    maxRelative (T rho) (T sigma) ≤ maxRelative rho sigma := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P21

end

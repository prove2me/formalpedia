-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P21_zeroTypeI_optimal_test
-- name    : QAlgorithms.Papers.Independent.Support50.P21.zeroTypeI_optimal_test
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T20:50:40.825538+00:00
-- url     : https://prove2.me/theorems/c2cee9c5-949f-4be6-b74d-404dd5763ac8
-- title:
--   §I/§IV: min-relative entropy as zero-type-I testing exponent
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces, and logarithms have base two.
--
--   For density operators $\rho,\sigma$, let $\pi_\rho$ be the support projector of $\rho$. This is an effect with zero type-I error $\operatorname{Tr}[(I-\pi_\rho)\rho]=0$. For every effect $P$ with $\operatorname{Tr}[(I-P)\rho]=0$,
--
--   $$\operatorname{Tr}(\pi_\rho\sigma)\le\operatorname{Tr}(P\sigma),\qquad D_{\min}(\rho\Vert\sigma)=-\log_2\operatorname{Tr}(\pi_\rho\sigma).$$
--
--   Thus the minimum type-II error is achieved by the support test, with no factor one half. Orthogonal states give zero type-II error and infinite divergence. This is the zero-type-I operational interpretation.
-- source:
--   Min- and Max- Relative Entropies and a New Entanglement Monotone, arXiv:0803.2770v3, PDF p. 2, §I/§IV: min-relative entropy as zero-type-I testing exponent

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

/-- PDF pp.2,6: optimal type-II error with ZERO type-I error, with an achieving
support-projector test. There is no equal-prior factor 1/2 in the type-II error. -/
theorem zeroTypeI_optimal_test (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    IsEffect (support rho) ∧ tr ((1 - support rho) * rho) = 0 ∧
    (∀ P : Mat I, IsEffect P → tr ((1 - P) * rho) = 0 →
      tr (support rho * sigma) ≤ tr (P * sigma)) ∧
    dMin rho sigma = -elog (tr (support rho * sigma)) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P21

end

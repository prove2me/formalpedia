-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P21_nonnegative_and_zero
-- name    : QAlgorithms.Papers.Independent.Support50.P21.nonnegative_and_zero
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T20:43:04.322795+00:00
-- url     : https://prove2.me/theorems/e17b25ee-a206-4935-8ad5-3c66dc83c034
-- title:
--   Lemma 6
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces, and logarithms have base two.
--
--   For density operators $\rho,\sigma$,
--
--   $$D_{\min}(\rho\Vert\sigma)\ge0,\qquad D_{\max}(\rho\Vert\sigma)\ge0,$$
--   $$D_{\min}(\rho\Vert\rho)=D_{\max}(\rho\Vert\rho)=0.$$
--
--   Moreover, equal supports imply $D_{\min}(\rho\Vert\sigma)=0$. No converse for the latter implication is asserted. These are the paper's normalization and zero-value properties.
-- source:
--   Min- and Max- Relative Entropies and a New Entanglement Monotone, arXiv:0803.2770v3, PDF p. 4, Lemma 6

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

/-- Lemma 6, PDF p.4: all clauses, without an incorrect converse for Dmin. -/
theorem nonnegative_and_zero (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    0 ≤ dMin rho sigma ∧ 0 ≤ maxRelative rho sigma ∧ dMin rho rho = 0 ∧ maxRelative rho rho = 0 ∧
    (support rho = support sigma → dMin rho sigma = 0) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P21

end

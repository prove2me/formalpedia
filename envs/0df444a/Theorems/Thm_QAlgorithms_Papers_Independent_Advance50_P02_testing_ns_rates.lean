-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_testing_ns_rates
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.testing_ns_rates
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:33:47.919933+00:00
-- url     : https://prove2.me/theorems/83ab3356-2545-4382-b32f-45f3242c10c2
-- title:
--   Quantum and NS classical testing rates agree
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. Let $(\rho_n,\sigma_n)$ be arbitrary finite normalized pairs, with full spectral decompositions at every $n$ and associated NS distributions $P_n,Q_n$. Assume either the number of distinct eigenvalues of $\sigma_n$ is eventually bounded by $C n^d$, or the negative logarithm of its smallest eigenvalue is so bounded. Constants $C>0$, $d$ and the threshold precede $n$. In the second alternative, a supported restriction is allowed only with explicit $\operatorname{supp}\rho_n\subseteq\operatorname{supp}\sigma_n$. For $0\le\varepsilon\le1$, let $B$ optimize liminf actual type-II exponent under limsup actual type-I error at most $\varepsilon$, and let $B^\dagger$ use liminf type-I error strictly below $\varepsilon$. Then
--   $$B(\varepsilon|\vec\rho\Vert\vec\sigma)=B(\varepsilon|\vec P\Vert\vec Q),\qquad B^\dagger(\varepsilon|\vec\rho\Vert\vec\sigma)=B^\dagger(\varepsilon|\vec P\Vert\vec Q).$$
--   The classical problem permits randomized tests and is represented by testing diagonal states. No iid or positive-variance condition is imposed. These equalities transfer the operational rates to classical hypothesis testing.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 23, §VIII: quantum/classical NS operational equivalence

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P02

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Advance50.P02

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63
  (Mat tensorPower logTwo normalQuantile testingBeta)

open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded supportPower)

open QAlgorithms (effectProb)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)

open QAlgorithms.Papers.Independent.Information100.P67 (purifiedDistance)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch)

variable {I J A B X Z : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype X] [DecidableEq X]
  [Fintype Z] [DecidableEq Z]

/-- Section VIII, PDF p.23: operational quantum/classical NS equivalence,
under the stated sufficient spectral control, without iid or positive variance. Source correction. Printed: The second spectral alternative p.23 refers to the minimum eigenvalue of sigma_n.
Changed: On a supported restriction use the smallest strictly positive eigenvalue with explicit support inclusion; retain the unrestricted distinct-eigenvalue branch.
Why: The common support restriction removes unused kernel directions and preserves quantum testing rates; discarded NS coordinates have zero P. This avoids treating log(0) as a finite spectral bound. -/
theorem testing_ns_rates (S : PairSequence) (hS : StateSequence S)
    (hcontrol : SpectralControl S) (r : ∀ k, PositiveSpectralPresentation (S.rho k))
    (s : ∀ k, PositiveSpectralPresentation (S.sigma k)) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1) :
    operationalTestingRate S e false = operationalTestingRate (nsSequence S r s) e false ∧
    operationalTestingRate S e true = operationalTestingRate (nsSequence S r s) e true := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_testing_operational_entropic_rates
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.testing_operational_entropic_rates
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:32:55.630756+00:00
-- url     : https://prove2.me/theorems/104e58b8-1aa6-4053-b1e1-c9ff9d5143f9
-- title:
--   Operational testing rates from one-shot testing entropies
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. Let $(\rho_n,\sigma_n)$ be arbitrary finite-dimensional normalized pairs, and $0\le\varepsilon\le1$. For every sequence of actual effects $0\le Q_n\le I$, let $a_n=\operatorname{tr}\rho_n(I-Q_n)$ and $r(Q)=\liminf_n[-\log\operatorname{tr}\sigma_nQ_n]/n$. Define $B^\varepsilon=\sup\{r(Q):\limsup a_n\le\varepsilon\}$ and $B^{\dagger,\varepsilon}=\sup\{r(Q):\liminf a_n<\varepsilon\}$. Then
--   $$B^\varepsilon=\sup_{\limsup\varepsilon_n\le\varepsilon}\liminf_n\frac1nD_h^{\varepsilon_n}(\rho_n\Vert\sigma_n),$$
--   $$B^{\dagger,\varepsilon}=\inf\{R:\forall Q,\ r(Q)\ge R\Rightarrow\liminf a_n\ge\varepsilon\}=\sup_{\liminf\varepsilon_n<\varepsilon}\liminf_n\frac1nD_h^{\varepsilon_n}(\rho_n\Vert\sigma_n).$$
--   The error sequences range over $[0,1]$, and zero type-II error gives infinite exponent. These are operational identities using actual effects, not free rate parameters.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 23, §VIII: testing operational/one-shot rate identities

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

/-- Section VIII, PDF p.23: actual effects and actual errors in both constraints,
including the universal converse formulation; no real-valued endpoint defaults. -/
theorem testing_operational_entropic_rates (S : PairSequence) (hS : StateSequence S)
    (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1) :
    operationalTestingRate S e false =
      optimizedEntropySequenceRate (fun k a => extendedTestingDivergence a (S.rho k) (S.sigma k)) e false ∧
    operationalTestingRate S e true = testingConverseRate S e ∧
    operationalTestingRate S e true =
      optimizedEntropySequenceRate (fun k a => extendedTestingDivergence a (S.rho k) (S.sigma k)) e true := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end

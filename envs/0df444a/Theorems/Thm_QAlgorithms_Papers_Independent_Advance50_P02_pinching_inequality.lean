-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_pinching_inequality
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.pinching_inequality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:20:16.880256+00:00
-- url     : https://prove2.me/theorems/8aa96ddb-a5fd-40af-a90c-cecda2844a56
-- title:
--   Pinching inequality
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. Let $\rho,\sigma\ge0$. For each distinct eigenvalue $v$ of $\sigma$, let $P_v$ project onto its entire eigenspace, including the zero eigenspace if present. Put $\mathcal E_\sigma(\rho)=\sum_vP_v\rho P_v$ and let $\nu(\sigma)$ count distinct eigenvalues. Then
--   $$\rho\le\nu(\sigma)\mathcal E_\sigma(\rho).$$
--   The factor counts eigenspaces rather than eigenvalue multiplicities.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 13, Lemma 11: pinching inequality

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

/-- Lemma 11, PDF pp.13--14, background Lemma 9 of [13]. -/
theorem pinching_inequality (rho sigma : Mat I) (hrho : rho.PosSemidef)
    (hsigma : sigma.PosSemidef) :
    Below rho ((distinctCount sigma : ℂ) • pinch sigma rho) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end

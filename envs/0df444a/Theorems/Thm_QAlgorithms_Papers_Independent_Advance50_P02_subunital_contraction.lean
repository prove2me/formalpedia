-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_subunital_contraction
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.subunital_contraction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:12:29.877779+00:00
-- url     : https://prove2.me/theorems/bb352597-30cc-4b21-b1a7-67d2cbb4eb20
-- title:
--   Sub-unital completely positive maps contract positive-operator norm
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. Let $A\ge0$ and let $\mathcal E:L(H)\to L(H')$ be complex linear and completely positive, with $\mathcal E(I)\le I$. Then
--   $$\|\mathcal E(A)\|_\infty\le\|A\|_\infty.$$
--   The norm is the largest singular value. This contraction controls positive testing objectives.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 7, Lemma 1: sub-unital CP operator-norm contraction

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

/-- Lemma 1, PDF p.7: Schatten infinity norm, not entrywise matrix norm. -/
theorem subunital_contraction (rho : Mat I) (hrho : rho.PosSemidef)
    (E : Mat I →ₗ[ℂ] Mat J) (hcp : QAlgorithms.Entanglement.IsCompletelyPositive E)
    (hsub : Below (E 1) 1) : ‖E rho‖ ≤ ‖rho‖ := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end

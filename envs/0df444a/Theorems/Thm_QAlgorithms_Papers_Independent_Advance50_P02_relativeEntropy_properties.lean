-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_relativeEntropy_properties
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.relativeEntropy_properties
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:27:15.147563+00:00
-- url     : https://prove2.me/theorems/178aeb44-c54a-48fa-a493-dcae743e6e5c
-- title:
--   Processing, order and scaling of relative entropies
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. For each entropy use its defining domain: $D_h$ has normalized $\rho$, positive $\sigma$ and $0\le\varepsilon\le1$; $D_{\max}$ uses normalized $\rho$ and $0\le\varepsilon<1$; $D_s$ allows $0<\operatorname{tr}\rho\le1$ and $0\le\varepsilon\le1$. For a trace-preserving completely positive map $\mathcal E$,
--   $$D_x^\varepsilon(\rho\Vert\sigma)\ge D_x^\varepsilon(\mathcal E(\rho)\Vert\mathcal E(\sigma)),\qquad x=h,\max.$$
--   If $0\le\sigma\le\sigma'$, then
--   $$D_x^\varepsilon(\rho\Vert\sigma)\ge D_x^\varepsilon(\rho\Vert\sigma'),\qquad x=h,\max,$$
--   and the corrected clause for $x=s$ requires $\rho$, $\sigma$ and $\sigma'$ to commute pairwise. For every real $\lambda$,
--   $$D_x^\varepsilon(\rho\Vert 2^{-\lambda}\sigma)=D_x^\varepsilon(\rho\Vert\sigma)+\lambda,\qquad x=h,\max,s.$$
--   Each clause retains its own full endpoint domain. These rules provide the structural comparisons used in the hierarchy.
--   Source correction: the spectrum comparison-order clause assumes pairwise commutation of $\rho,\sigma,\sigma^{\prime}$. The printed premise only requires $\sigma$ and $\sigma^{\prime}$ to commute and is false; the two-dimensional witness and the precise printed/changed/why record are included in this item. No commutation premise is added to the testing or max-relative-entropy clauses.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 13, §V Eqs. (11)–(13): processing, order, scaling

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

/-- Eqs.(11)--(13), PDF p.13: each entropy retains its own full error and
state domain. Source correction of the Ds comparison-order clause only.
Printed: Section V p.13, after Eq.(12), says comparison monotonicity extends to Ds when sigma and sigma2 commute, without requiring either to commute with rho.
Changed: Only the Ds comparison-order clause additionally requires Commute rho sigma and Commute rho sigma2, so all three operators have a common eigenbasis. The other seven clauses and every defining domain remain unchanged.
Why: Commuting comparisons alone are insufficient. Take rho=(1/2)*[[1,1],[1,1]], sigma=diag(4/5,1/10), sigma2=diag(4/5,1/5), and e=2/25. Then sigma<=sigma2 and the comparisons commute, but Ds^e(rho||sigma2)-Ds^e(rho||sigma)=log2(7/6)>0, reversing the printed order. The common-eigenbasis hypotheses restore the classical threshold inclusion underlying inspection of the definitions. They are local to this clause and admit nontrivial diagonal states and comparisons. -/
theorem relativeEntropy_properties :
    (∀ (rho sigma : Mat I), QAlgorithms.IsDensityMatrix rho → sigma.PosSemidef →
      ∀ (E : Mat I →ₗ[ℂ] Mat J), QAlgorithms.Entanglement.IsCompletelyPositive E →
      TracePreserving E → ∀ e : ℝ, 0 ≤ e ∧ e ≤ 1 →
      extendedTestingDivergence e (E rho) (E sigma) ≤ extendedTestingDivergence e rho sigma) ∧
    (∀ (rho sigma : Mat I), QAlgorithms.IsDensityMatrix rho → sigma.PosSemidef →
      ∀ (E : Mat I →ₗ[ℂ] Mat J), QAlgorithms.Entanglement.IsCompletelyPositive E →
      TracePreserving E → ∀ e : ℝ, 0 ≤ e ∧ e < 1 →
      smoothedMaxRelativeEntropy e (E rho) (E sigma) ≤ smoothedMaxRelativeEntropy e rho sigma) ∧
    (∀ (rho sigma sigma2 : Mat I), QAlgorithms.IsDensityMatrix rho → sigma.PosSemidef →
      sigma2.PosSemidef → Below sigma sigma2 → ∀ e : ℝ, 0 ≤ e ∧ e ≤ 1 →
      extendedTestingDivergence e rho sigma2 ≤ extendedTestingDivergence e rho sigma) ∧
    (∀ (rho sigma sigma2 : Mat I), QAlgorithms.IsDensityMatrix rho → sigma.PosSemidef →
      sigma2.PosSemidef → Below sigma sigma2 → ∀ e : ℝ, 0 ≤ e ∧ e < 1 →
      smoothedMaxRelativeEntropy e rho sigma2 ≤ smoothedMaxRelativeEntropy e rho sigma) ∧
    (∀ (rho sigma sigma2 : Mat I), PositiveTraceSubnormalized rho → sigma.PosSemidef →
      sigma2.PosSemidef → Below sigma sigma2 → Commute sigma sigma2 →
      Commute rho sigma → Commute rho sigma2 → ∀ e : ℝ, 0 ≤ e ∧ e ≤ 1 →
      spectrumEntropy e rho sigma2 ≤ spectrumEntropy e rho sigma) ∧
    (∀ (rho sigma : Mat I), QAlgorithms.IsDensityMatrix rho → sigma.PosSemidef →
      ∀ e : ℝ, 0 ≤ e ∧ e ≤ 1 → ∀ l : ℝ,
      extendedTestingDivergence e rho (((Real.rpow 2 (-l) : ℝ) : ℂ) • sigma) =
        extendedTestingDivergence e rho sigma + (l : EReal)) ∧
    (∀ (rho sigma : Mat I), QAlgorithms.IsDensityMatrix rho → sigma.PosSemidef →
      ∀ e : ℝ, 0 ≤ e ∧ e < 1 → ∀ l : ℝ,
      smoothedMaxRelativeEntropy e rho (((Real.rpow 2 (-l) : ℝ) : ℂ) • sigma) =
        smoothedMaxRelativeEntropy e rho sigma + (l : EReal)) ∧
    (∀ (rho sigma : Mat I), PositiveTraceSubnormalized rho → sigma.PosSemidef →
      ∀ e : ℝ, 0 ≤ e ∧ e ≤ 1 → ∀ l : ℝ,
      spectrumEntropy e rho (((Real.rpow 2 (-l) : ℝ) : ℂ) • sigma) =
        spectrumEntropy e rho sigma + (l : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end

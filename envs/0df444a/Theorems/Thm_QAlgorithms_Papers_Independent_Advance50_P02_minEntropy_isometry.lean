-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_minEntropy_isometry
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.minEntropy_isometry
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:13:42.617687+00:00
-- url     : https://prove2.me/theorems/2e984590-556d-41bd-bd67-355346590dd2
-- title:
--   Smooth min-entropy isometry invariance
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. Let $\rho_{AB}\ge0$ satisfy $0<\operatorname{tr}\rho_{AB}\le1$, let $U:A\to A'$ satisfy $U^\dagger U=I_A$, and let $0\le\varepsilon<1$. Put $\tau=(U\otimes I_B)\rho(U^\dagger\otimes I_B)$. With purified-distance smoothing over positive-trace subnormalized states and optimization over normalized reference states on $B$,
--   $$H_{\min}^\varepsilon(A|B)_\rho=H_{\min}^\varepsilon(A'|B)_\tau.$$
--   Thus changing the isometric realization of the first system preserves this entropy.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 8, Lemma 2: smooth min-entropy isometry invariance

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

/-- Lemma 2, PDF p.8, citing [37],[35]: subnormalized centers allowed. Source correction. Printed: Definition 3 p.8 says normalized centers, but Lemma 2 and Proposition 3 explicitly allow positive-trace subnormalized centers.
Changed: Use the same purified-distance smoothing and normalized-reference optimization on positive-trace subnormalized centers, with extended-real extrema.
Why: This matches the explicit result domain without dropping subnormalized inputs or adding normalization. -/
theorem minEntropy_isometry (rho : Mat (A × B)) (hrho : PositiveTraceSubnormalized rho)
    (U : Matrix I A ℂ) (hU : Uᴴ * U = 1) (e : ℝ) (he : 0 ≤ e ∧ e < 1) :
    positiveTraceSmoothedMinEntropy e rho = positiveTraceSmoothedMinEntropy e
      (liftIsometry (B := B) U * rho * (liftIsometry (B := B) U)ᴴ) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end

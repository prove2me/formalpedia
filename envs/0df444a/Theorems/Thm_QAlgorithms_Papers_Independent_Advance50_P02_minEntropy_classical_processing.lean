-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_minEntropy_classical_processing
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.minEntropy_classical_processing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:14:23.694374+00:00
-- url     : https://prove2.me/theorems/99688053-8c6b-4992-b46b-ac6de3ae9ed0
-- title:
--   Classical processing of smooth min-entropy
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. Let $\rho_{XAB}=\sum_x|x\rangle\langle x|\otimes R^x_{AB}$, where every block is positive and $0<\sum_x\operatorname{tr}R^x\le1$. Let $f:X\to Z$ be arbitrary and form $\tau_{ZAB}=\sum_z|z\rangle\langle z|\otimes\sum_{x:f(x)=z}R^x$. For $0\le\varepsilon<1$,
--   $$H_{\min}^\varepsilon(XA|B)_\rho\ge H_{\min}^\varepsilon(ZA|B)_\tau.$$
--   This permits many-to-one classical postprocessing while retaining the quantum system $A$.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 8, Proposition 3: classical processing of smooth min-entropy

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

/-- Proposition 3, PDF p.8: arbitrary f, retaining the quantum A. Source correction. Printed: Definition 3 p.8 says normalized centers, but Lemma 2 and Proposition 3 explicitly allow positive-trace subnormalized centers.
Changed: Use the same purified-distance smoothing and normalized-reference optimization on positive-trace subnormalized centers, with extended-real extrema.
Why: This matches the explicit result domain without dropping subnormalized inputs or adding normalization. -/
theorem minEntropy_classical_processing (blocks : X → Mat (A × B))
    (hblocks : ∀ x, (blocks x).PosSemidef)
    (htrace : 0 < ∑ x, (blocks x).trace.re ∧ (∑ x, (blocks x).trace.re) ≤ 1)
    (f : X → Z) (e : ℝ) (he : 0 ≤ e ∧ e < 1) :
    positiveTraceSmoothedMinEntropy e (joinClassical blocks) ≥
      positiveTraceSmoothedMinEntropy e (joinClassical (processBlocks f blocks)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end

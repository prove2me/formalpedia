-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P35_copositiveZero
-- name    : QAlgorithms.Papers.Independent.Claimed50.P35.copositiveZero
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:30:58.925489+00:00
-- url     : https://prove2.me/theorems/b4e6aff0-9703-45bd-b7db-d66244d3b577
-- title:
--   II.B: completely copositive zero bound
-- statement:
--   Let $T$ be a full trace-class CPTP channel between nonzero Hilbert spaces. Suppose $T\circ\Theta$ is completely positive, where $\Theta$ transposes the input. Then
--
--   $$Q_\Theta(T)=Q(T)=Q_\epsilon(T)=0\quad(0\le\epsilon<1).$$
--
--   Trace preservation already follows from $T$ and transposition; requiring the composite to be a channel expresses precisely this additional complete positivity. The conclusion gives a zero-capacity criterion independent of energy constraints.
-- source:
--   Evaluating Capacities of Bosonic Gaussian Channels, arXiv:quant-ph/9912067v1, PDF p. 4, II.B: completely copositive zero bound

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Claimed50.P35

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39
  (displacementMatrix attenuatorMatrix amplifierMatrix thermalMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation conjugateKernel composeKernel partialRight isometryCoeff identityCoeff)

open QAlgorithms.Papers.Independent.Frontier30.P21 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

/-- II.B, p.4: complete copositivity forces zero. TP of T makes CP of
T o transpose equivalent to that composite being a channel. -/
theorem copositiveZero {I J : Type} [Nonempty I] [Nonempty J]
    (T : Operation I J) (hT : IsTraceClassChannel T)
    (hcopositive : IsTraceClassChannel (T ∘ transpose)) :
    transposeBound T = 0 ∧ traceClassQuantumCapacity T = 0 ∧
    ∀ eps : ℝ, 0 ≤ eps → eps < 1 → epsilonCapacity T eps = 0 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P35

end

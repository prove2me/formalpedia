-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P35_transposeBound_bottleneck
-- name    : QAlgorithms.Papers.Independent.Claimed50.P35.transposeBound_bottleneck
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:29:08.89134+00:00
-- url     : https://prove2.me/theorems/559e4640-187c-4eb3-b014-7d5803d63f52
-- title:
--   II.B: bottleneck inequality
-- statement:
--   Let $T$ and $S$ be composable CPTP channels on full trace class over nonzero completed complex Hilbert spaces. Then
--
--   $$Q_\Theta(S\circ T)\le\min\{Q_\Theta(S),Q_\Theta(T)\}.$$
--
--   The transpose bound uses input transposition, the completely bounded trace norm without a half factor, and logarithms in bits. Infinite values are allowed. The inequality expresses the bound's bottleneck property under serial composition.
-- source:
--   Evaluating Capacities of Bosonic Gaussian Channels, arXiv:quant-ph/9912067v1, PDF p. 4, II.B: bottleneck inequality

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

/-- II.B, p.4: bottleneck bound for composable channels. -/
theorem transposeBound_bottleneck {I J K : Type}
    [Nonempty I] [Nonempty J] [Nonempty K]
    (S : Operation J K) (T : Operation I J)
    (hS : IsTraceClassChannel S) (hT : IsTraceClassChannel T) :
    transposeBound (S ∘ T) ≤ min (transposeBound S) (transposeBound T) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P35

end

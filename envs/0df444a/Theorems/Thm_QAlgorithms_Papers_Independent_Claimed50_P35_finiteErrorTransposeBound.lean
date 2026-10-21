-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P35_finiteErrorTransposeBound
-- name    : QAlgorithms.Papers.Independent.Claimed50.P35.finiteErrorTransposeBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:27:41.17038+00:00
-- url     : https://prove2.me/theorems/00682703-a088-4ff3-b042-e46bacb6f4df
-- title:
--   II.B, Eq.(2.9): finite-error transpose capacity bound
-- statement:
--   Let $T$ be any complex-linear completely positive trace-preserving map on full Hilbert-space trace class, and let $0\le\epsilon<1$. Define $Q_\epsilon$ by fixed encoding and decoding channels on every sequence of block lengths tending to infinity, with eventual completely bounded trace-norm error at most $\epsilon$. All logarithms are base two, and no factor $1/2$ occurs in the norm. Then
--
--   $$Q_\epsilon(T)\le Q_\Theta(T):=\log_2\|T\circ\Theta\|_\diamond,\qquad Q(T)\le Q_\Theta(T).$$
--
--   For $\epsilon>0$, also $Q(T)\le Q_\epsilon(T)$. Here $\Theta$ is input basis transposition, $Q$ uses vanishing error, and the values may be infinite. This supplies a bound even for fixed nonzero transmission error.
-- source:
--   Evaluating Capacities of Bosonic Gaussian Channels, arXiv:quant-ph/9912067v1, PDF p. 3, II.B, Eq.(2.9): finite-error transpose capacity bound

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

/-- II.B, (2.9), pp.3--4. Q<=Q_epsilon requires epsilon>0: vanishing
error does not imply eventual exact zero error. Both upper bounds include epsilon=0. -/
theorem finiteErrorTransposeBound {I J : Type} [Nonempty I] [Nonempty J]
    (T : Operation I J) (hT : IsTraceClassChannel T)
    (eps : ℝ) (heps : 0 ≤ eps) (heps1 : eps < 1) :
    epsilonCapacity T eps ≤ transposeBound T ∧ traceClassQuantumCapacity T ≤ transposeBound T ∧
    (0 < eps → traceClassQuantumCapacity T ≤ epsilonCapacity T eps) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P35

end

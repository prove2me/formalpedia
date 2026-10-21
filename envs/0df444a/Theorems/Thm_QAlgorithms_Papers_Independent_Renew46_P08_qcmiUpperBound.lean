-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_qcmiUpperBound
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.qcmiUpperBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:47:45.78262+00:00
-- url     : https://prove2.me/theorems/ddbac420-28a9-4fb4-a142-0f3093ca964b
-- title:
--   Unnumbered four-entropy upper bound (17)
-- statement:
--   For every normalized tripartite state $\rho_{ABC}$ on nonzero separable complex Hilbert systems, with entropy and QCMI defined as extended nonnegative quantities in nats,
--
--   $$I(A:B|C)_\rho\le2\min\{H(\rho_A),H(\rho_B),H(\rho_{AC}),H(\rho_{BC})\}.$$
--
--   All marginals are partial traces. In particular, finiteness of any one of these four entropies establishes QCMI finiteness.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 8, Unnumbered four-entropy upper bound (17)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P08

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Renew46.P08

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (CountableStateEnsemble convexOperatorMixture)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity traceSize tensorApply productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble averageCoefficients extendedEntropyNats
    extendedRelativeEntropyNats ensembleHolevo)

open QAlgorithms.Papers.Independent.Frontier18.P08
  (partialTraceFirst partialTraceSecond operatorTrace)

open QAlgorithms.Papers.Independent.Frontier30.P14 (conjugateKernel)

open QAlgorithms.Papers.Independent.Claimed50.P07
  (boundedCoefficients oscillatorGround oscillatorLevels oscillatorEnvelope oscillatorEntropyBounded)

open QAlgorithms.Papers.Independent.Next46.P08 (continuityRatio MajorantRegularity)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- PDF p.8, (17): all FOUR marginal entropies, with extended values allowed. -/
theorem qcmiUpperBound {I J K : Type} [Countable I] [Countable J] [Countable K]
    [Nonempty I] [Nonempty J] [Nonempty K] (rho : State (I × (J × K))) :
    qcmi rho.coefficients ≤ 2 * min
      (min (extendedEntropyNats (partialTraceSecond rho.coefficients))
        (extendedEntropyNats (partialTraceSecond (partialTraceFirst rho.coefficients))))
      (min (extendedEntropyNats (countableMarginalAC rho.coefficients))
        (extendedEntropyNats (partialTraceFirst rho.coefficients))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_qcmiMixing
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.qcmiMixing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:49:03.598511+00:00
-- url     : https://prove2.me/theorems/60813761-3f40-44a2-abb0-b6d0249451f5
-- title:
--   Unnumbered almost-affinity inequality (18)
-- statement:
--   Let $\rho,\sigma$ be tripartite states with finite QCMI and $0<p<1$. For their actual mixture $\omega=p\rho+(1-p)\sigma$,
--
--   $$pI(A:B|C)_\rho+(1-p)I(A:B|C)_\sigma\le I(A:B|C)_\omega+h_2(p).$$
--
--   The inequality is expressed additively in extended nonnegative values. It requires neither finite individual marginal entropies nor a separate assumption on the mixture's entropy, and records the source's almost-affinity property.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 8, Unnumbered almost-affinity inequality (18)

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

/-- PDF p.8, (18): additive extended form of almost-affinity. Only QCMI of
the two component states is assumed finite; no finite marginal entropies. -/
theorem qcmiMixing {I J K : Type} [Countable I] [Countable J] [Countable K]
    [Nonempty I] [Nonempty J] [Nonempty K] (rho sigma : State (I × (J × K)))
    (hrho : qcmi rho.coefficients < ⊤) (hsigma : qcmi sigma.coefficients < ⊤)
    (p : ℝ) (hp : 0 < p) (hpone : p < 1) :
    ENNReal.ofReal p * qcmi rho.coefficients + ENNReal.ofReal (1-p) * qcmi sigma.coefficients ≤
      qcmi (convexOperatorMixture p rho.coefficients sigma.coefficients) + ENNReal.ofReal (Real.binEntropy p) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end

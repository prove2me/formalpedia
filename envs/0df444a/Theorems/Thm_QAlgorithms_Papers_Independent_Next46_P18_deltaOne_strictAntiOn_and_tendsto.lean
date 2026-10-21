-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_deltaOne_strictAntiOn_and_tendsto
-- name    : QAlgorithms.Papers.Independent.Next46.P18.deltaOne_strictAntiOn_and_tendsto
-- status  : Proved
-- author  : @Imine
-- created : 2026-10-21T01:36:03.305961+00:00
-- url     : https://prove2.me/theorems/47d20684-e2f6-4370-a71c-eeca2b21c31f
-- title:
--   Monotonicity and vanishing limit of the one-mode Gaussian information deficit
-- statement:
--   Fix $E>0$, $v>0$ and define, for $P\ge 1/(4E)$,
--   $$
--   \delta_1(P)=g\!\left(\sqrt{EP+\frac{E}{4v}}-\frac12\right)-g\!\left(\sqrt{EP}-\frac12\right),
--   \qquad
--   g(x)=(x+1)\log(x+1)-x\log x .
--   $$
--   Then $\delta_1$ is strictly decreasing on $[1/(4E),\infty)$ and
--   $$
--   \lim_{P\to+\infty}\delta_1(P)=0 .
--   $$
--   This is the scalar analytic content of the one-mode Gaussian limiting-deficit statement: the deficit is positive, decreases monotonically as the momentum variance grows, and vanishes in the limit. It is independent of the channel and of any quantum-state construction.
-- source:
--   Holevo, Gaussian classical-quantum channels: gain of entanglement-assistance, arXiv:1211.4774v1, PDF pp.14-15; scalar deficit delta_1 defined in the platform file Def_QAlgorithms_Papers_Independent_Next46_P18.

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P18

noncomputable section

open Filter MeasureTheory

open scoped ENNReal Topology BigOperators ComplexOrder BoundedContinuousFunction

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Frontier18.P01
  (Channel homogeneousEntropy mutualInformation boundedConjugation traceFirst traceSecond)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)

open QAlgorithms.Papers.Independent.Frontier30.P10 (HilbertPOVM)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (ScaledWeylRepresentation InterleavedPhase physicalCommutationMatrix
   gaussianFunction weylTraceCharacteristic tracePair)

open QAlgorithms.Papers.Independent.Claimed50.P13
  (PositiveObservable zeroObservable feasibleStates informationSupremum
   operationalAssistedCapacity regularizedUnassistedCapacity)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex quantumCovariance)

namespace QAlgorithms.Papers.Independent.Next46.P18

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-- The scalar deficit `deltaOne E v P` is strictly decreasing for
`P >= 1/(4E)` and tends to zero as `P -> infinity`. -/
theorem deltaOne_strictAntiOn_and_tendsto {E v : ℝ} (hE : 0 < E) (hv : 0 < v) :
    StrictAntiOn (deltaOne E v) (Set.Ici (1 / (4 * E))) ∧
    Tendsto (deltaOne E v) atTop (𝓝 0) := by sorry

end QAlgorithms.Papers.Independent.Next46.P18

end

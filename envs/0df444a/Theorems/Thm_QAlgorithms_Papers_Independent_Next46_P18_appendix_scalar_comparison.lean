-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_appendix_scalar_comparison
-- name    : QAlgorithms.Papers.Independent.Next46.P18.appendix_scalar_comparison
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T15:17:59.908665+00:00
-- url     : https://prove2.me/theorems/7795f7c5-e75f-4830-b4bf-24d35d302bd3
-- title:
--   §5.2, explicit scalar comparison underlying the claimed gain
-- statement:
--   For $x\ge1$ define $f_1(x)=\log x$ and $f_2(x)=((x+1)/2)\log((x+1)/2)-((x-1)/2)\log((x-1)/2)$, with $0\log0=0$. Then $f_1(1)=f_2(1)$, both first derivatives tend to zero at $+\infty$, and
--
--   $$f_1''(x)>f_2''(x),\qquad f_1(x)<f_2(x)\quad(x>1).$$
--
--   This is a scalar comparison in natural logarithms. It does not identify $f_1$ with the operational unassisted capacity of the quantum-output channel.
-- source:
--   Gaussian classical-quantum channels: gain of entanglement-assistance, arXiv:1211.4774v1, PDF p. 17, §5.2, explicit scalar comparison underlying the claimed gain

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

/-- Holevo arXiv:1211.4774v1, PDF p.17, Appendix 2: named scalar comparison.
Derivative comparisons have domain x>1. No physical capacity is identified with f1. -/
theorem appendix_scalar_comparison :
    fOne 1 = fTwo 1 ∧
    Tendsto (deriv fOne) atTop (𝓝 0) ∧ Tendsto (deriv fTwo) atTop (𝓝 0) ∧
    (∀ x : ℝ, 1 < x → deriv (deriv fTwo) x < deriv (deriv fOne) x) ∧
    (∀ x : ℝ, 1 < x → fOne x < fTwo x) := by sorry

end QAlgorithms.Papers.Independent.Next46.P18

end

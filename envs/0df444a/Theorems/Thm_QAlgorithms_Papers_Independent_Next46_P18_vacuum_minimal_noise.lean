-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_vacuum_minimal_noise
-- name    : QAlgorithms.Papers.Independent.Next46.P18.vacuum_minimal_noise
-- status  : Proved
-- author  : @Imine
-- created : 2026-10-21T02:52:11.130371+00:00
-- url     : https://prove2.me/theorems/5a1434c9-57e7-4d4a-9aed-8d169b4d0af6
-- title:
--   One-mode vacuum covariance is minimal physical noise
-- statement:
--   Let $\Omega_1$ be the canonical symplectic matrix on the one-mode phase space $\mathbb{R}^2$, and let
--   $$
--   \alpha_0=\frac12\,\mathbf 1_2
--   $$
--   be the vacuum covariance. Then $\alpha_0$ is a minimal physical noise matrix: it satisfies the covariance inequality
--   $$
--   2\alpha_0\pm i\Omega_1\succeq0,
--   $$
--   and for every real symmetric $2\times2$ matrix $\beta$ with $2\beta\pm i\Omega_1\succeq0$ and $\alpha_0-\beta\succeq0$, one has $\beta=\alpha_0$.
--
--   Equivalently, the vacuum is the smallest covariance compatible with the canonical commutation relation. This is the one-mode uncertainty-principle fact used when the two-dimensional example is specialized to vacuum noise $\alpha=I_2/2$; it is independent of the signal and of the capacity definitions.
-- source:
--   Standard one-mode uncertainty-principle fact used in Holevo, Gaussian classical-quantum channels: gain of entanglement-assistance, arXiv:1211.4774v1, PDF pp.11-12, vacuum noise alpha=I_2/2.

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

/-- The one-mode vacuum covariance `(1/2) I` is a minimal physical noise
matrix: it satisfies the covariance inequality and no smaller symmetric
matrix does. -/
theorem vacuum_minimal_noise :
    MinimalNoise ((1 / 2 : ℝ) •
      (1 : Matrix (QuadratureIndex 1) (QuadratureIndex 1) ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P18

end

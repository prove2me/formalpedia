-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_squeezed_covariance_sequence
-- name    : QAlgorithms.Papers.Independent.Next46.P18.squeezed_covariance_sequence
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T15:13:41.440924+00:00
-- url     : https://prove2.me/theorems/ab45b052-6162-42a8-a3ff-db069b9e9843
-- title:
--   §3, unnumbered Lemma: squeezed physical covariance sequence
-- statement:
--   Let $s_A,s_B$ be finite mode counts, $\Delta_A$ the canonical real symplectic matrix, and $K:\mathbb R^{2s_B}\to\mathbb R^{2s_A}$ a real matrix with $K^{\mathsf T}\Delta_AK=0$. There is a sequence of real symmetric matrices $\gamma_n$ such that
--
--   $$\gamma_n\pm\frac i2\Delta_A\succeq0\quad\text{for every }n,\qquad K^{\mathsf T}\gamma_nK\longrightarrow0.$$
--
--   Convergence is in the finite-dimensional matrix topology. No noise covariance, rank-surjectivity or quantum-input assumption is required. Zero coupling and zero-dimensional phase spaces are allowed. The statement supplies physical squeezed covariances with arbitrarily small compressed fluctuations.
-- source:
--   Gaussian classical-quantum channels: gain of entanglement-assistance, arXiv:1211.4774v1, PDF p. 7, §3, unnumbered Lemma: squeezed physical covariance sequence

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

/-- Holevo arXiv:1211.4774v1, PDF pp.7-8, unnumbered Lemma.
Only compressed covariances converge. K=0 and zero mode counts are permitted. -/
theorem squeezed_covariance_sequence {s t : ℕ}
    (K : Matrix (QuadratureIndex s) (QuadratureIndex t) ℝ) (hisotropic : K.transpose * (physicalCommutationMatrix s 1) * K = 0) :
    ∃ gamma : ℕ → Matrix (QuadratureIndex s) (QuadratureIndex s) ℝ,
      (∀ n, quantumCovariance ((2 : ℝ) • gamma n)) ∧
      Tendsto (fun n => K.transpose * gamma n * K) atTop (𝓝 0) := by sorry

end QAlgorithms.Papers.Independent.Next46.P18

end

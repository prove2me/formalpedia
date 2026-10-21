-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_gaussian_cq_criterion
-- name    : QAlgorithms.Papers.Independent.Next46.P18.gaussian_cq_criterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:08:42.938591+00:00
-- url     : https://prove2.me/theorems/4139c48c-4e38-4eea-9063-36d39590d76c
-- title:
--   §3, unnumbered criterion (14): Gaussian c-q iff isotropic K
-- statement:
--   Let $\Phi$ be a centered Gaussian completely positive trace-preserving channel on nonzero separable complex Hilbert spaces carrying regular irreducible finite-mode Weyl representations. Use $\hbar=1$, interleaved quadratures, $\Delta=\bigoplus_j\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$, and the Weyl phase $\exp(-iz^{\mathsf T}\Delta w/2)$. Write $K:Z_B\to Z_A$ and $\alpha$ for its real coupling and symmetric noise, with $\alpha\pm i(\Delta_B-K^{\mathsf T}\Delta_AK)/2\succeq0$. States below are normalized positive trace-class operators, without a Fock cutoff. All entropies and capacities use natural logarithms.
--
--   The range of the full normal dual $\Phi^*:B(\mathcal H_B)\to B(\mathcal H_A)$ consists of mutually commuting operators if and only if
--
--   $$K^{\mathsf T}\Delta_AK=0.$$
--
--   Commutation is required for the images of every pair of bounded observables. Zero coupling is permitted. This characterizes Gaussian classical-quantum channels independently of a choice of Weyl generators.
-- source:
--   Gaussian classical-quantum channels: gain of entanglement-assistance, arXiv:1211.4774v1, PDF p. 5, §3, unnumbered criterion (14): Gaussian c-q iff isotropic K

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

/-- Holevo arXiv:1211.4774v1, PDF p.5, (14): c-q iff the coupling is isotropic.
This is commuting range of the entire normal dual, not a test only on Weyls. -/
theorem gaussian_cq_criterion {I J : Type} [Countable I] [Countable J]
    [Nonempty I] [Nonempty J] {s t : ℕ}
    (WA : ScaledWeylRepresentation I s 1) (WB : ScaledWeylRepresentation J t 1)
    (Phi : DualChannel I J) (K : Matrix (QuadratureIndex s) (QuadratureIndex t) ℝ)
    (alpha : Matrix (QuadratureIndex t) (QuadratureIndex t) ℝ) (hG : GaussianChannel WA WB Phi K alpha) :
    IsCQ Phi ↔ K.transpose * (physicalCommutationMatrix s 1) * K = 0 := by sorry

end QAlgorithms.Papers.Independent.Next46.P18

end

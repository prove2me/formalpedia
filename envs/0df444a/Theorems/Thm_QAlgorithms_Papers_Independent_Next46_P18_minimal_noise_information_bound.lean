-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_minimal_noise_information_bound
-- name    : QAlgorithms.Papers.Independent.Next46.P18.minimal_noise_information_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:12:09.983552+00:00
-- url     : https://prove2.me/theorems/0a461b87-425e-4c0b-84ac-64e21b996695
-- title:
--   Proposition 1, final clause (16): minimal-noise mutual-information bound
-- statement:
--   Let $\Phi$ be a centered Gaussian completely positive trace-preserving channel on nonzero separable complex Hilbert spaces carrying regular irreducible finite-mode Weyl representations. Use $\hbar=1$, interleaved quadratures, $\Delta=\bigoplus_j\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$, and the Weyl phase $\exp(-iz^{\mathsf T}\Delta w/2)$. Write $K:Z_B\to Z_A$ and $\alpha$ for its real coupling and symmetric noise, with $\alpha\pm i(\Delta_B-K^{\mathsf T}\Delta_AK)/2\succeq0$. States below are normalized positive trace-class operators, without a Fock cutoff. All entropies and capacities use natural logarithms.
--
--   Assume that $\Phi$ is classical-quantum with minimal noise: the centered Gaussian environment in the same minimal-mode dilation is pure. For every normal input state $\rho$,
--
--   $$I(\rho,\Phi)\le S(\Phi(\rho)).$$
--
--   Here $I$ is quantum mutual information defined by relative entropy of the channel output of a purification against the product of its marginals. This definition includes infinite-entropy inputs. The bound is the pure-environment consequence of the weak-complement entropy increase.
-- source:
--   Gaussian classical-quantum channels: gain of entanglement-assistance, arXiv:1211.4774v1, PDF p. 6, Proposition 1, final clause (16): minimal-noise mutual-information bound

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

/-- Holevo arXiv:1211.4774v1, PDF p.6, Proposition 1, (16).
Minimal noise means the environment in the same minimal-mode dilation is pure;
all normal inputs are included, even those with infinite entropy. -/
theorem minimal_noise_information_bound {I J D F : Type}
    [Countable I] [Countable J] [Countable D] [Countable F]
    [Nonempty I] [Nonempty J] [Nonempty D] [Nonempty F] {s t : ℕ}
    (WA : ScaledWeylRepresentation I s 1) (WB : ScaledWeylRepresentation J t 1)
    (Phi : DualChannel I J) (K : Matrix (QuadratureIndex s) (QuadratureIndex t) ℝ)
    (alpha : Matrix (QuadratureIndex t) (QuadratureIndex t) ℝ) (hG : GaussianChannel WA WB Phi K alpha)
    (hcq : IsCQ Phi) (d : GaussianDilation WA WB Phi K alpha D F)
    (hpure : ∃ u : Hilbert D, ‖u‖ = 1 ∧ d.environment.coefficients = rankOne u) :
    ∀ rho : State I, mutualInformation rho.coefficients Phi.predual.val ≤
      homogeneousEntropy (Phi.predual.val rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Next46.P18

end

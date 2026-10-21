-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_weak_complement_entropy_increase
-- name    : QAlgorithms.Papers.Independent.Next46.P18.weak_complement_entropy_increase
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:11:24.353192+00:00
-- url     : https://prove2.me/theorems/183c4a94-6af7-4ede-884e-fcd379b78a7c
-- title:
--   Proposition 1: nonnegative weak-complement entropy gain
-- statement:
--   Let $\Phi$ be a centered Gaussian completely positive trace-preserving channel on nonzero separable complex Hilbert spaces carrying regular irreducible finite-mode Weyl representations. Use $\hbar=1$, interleaved quadratures, $\Delta=\bigoplus_j\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$, and the Weyl phase $\exp(-iz^{\mathsf T}\Delta w/2)$. Write $K:Z_B\to Z_A$ and $\alpha$ for its real coupling and symmetric noise, with $\alpha\pm i(\Delta_B-K^{\mathsf T}\Delta_AK)/2\succeq0$. States below are normalized positive trace-class operators, without a Fock cutoff. All entropies and capacities use natural logarithms.
--
--   Assume that $\Phi$ is classical-quantum. Use its minimal-mode Gaussian unitary dilation $\mathcal H_A\otimes\mathcal H_D\simeq\mathcal H_B\otimes\mathcal H_E$, with $s_D=s_B$ and $s_E=s_A$, centered Gaussian environment $\rho_D$, and the symplectic blocks in (5)–(11). Let $\widetilde\Phi^{\mathrm w}$ be the partial trace over $B$ of this same unitary acting on $\rho\otimes\rho_D$. The environment may be mixed. For every normal input state,
--
--   $$S(\rho)\le S(\widetilde\Phi^{\mathrm w}(\rho)).$$
--
--   Entropy is extended nonnegative, so this also states the infinite-entropy case without subtracting infinities. It is the entropy-increase property of the specified weak complement.
-- source:
--   Gaussian classical-quantum channels: gain of entanglement-assistance, arXiv:1211.4774v1, PDF p. 5, Proposition 1: nonnegative weak-complement entropy gain

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

/-- Holevo arXiv:1211.4774v1, PDF pp.5-6, Proposition 1, mixed environment.
Entropy increase is an extended order assertion, without infinity-infinity. -/
theorem weak_complement_entropy_increase {I J D F : Type}
    [Countable I] [Countable J] [Countable D] [Countable F]
    [Nonempty I] [Nonempty J] [Nonempty D] [Nonempty F] {s t : ℕ}
    (WA : ScaledWeylRepresentation I s 1) (WB : ScaledWeylRepresentation J t 1)
    (Phi : DualChannel I J) (K : Matrix (QuadratureIndex s) (QuadratureIndex t) ℝ)
    (alpha : Matrix (QuadratureIndex t) (QuadratureIndex t) ℝ) (hG : GaussianChannel WA WB Phi K alpha)
    (hcq : IsCQ Phi) (d : GaussianDilation WA WB Phi K alpha D F) :
    ∀ rho : State I, homogeneousEntropy rho.coefficients ≤
      homogeneousEntropy (weakOutput d.unitary d.environment rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Next46.P18

end

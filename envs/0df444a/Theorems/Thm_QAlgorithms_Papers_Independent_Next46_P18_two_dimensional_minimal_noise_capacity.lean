-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_two_dimensional_minimal_noise_capacity
-- name    : QAlgorithms.Papers.Independent.Next46.P18.two_dimensional_minimal_noise_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:14:24.338103+00:00
-- url     : https://prove2.me/theorems/1e28842e-7591-48a9-aea8-6f23e8dfeab8
-- title:
--   §4.1, explicit main result (30): two-dimensional minimal-noise signal
-- statement:
--   Let $\Phi$ be a centered Gaussian completely positive trace-preserving channel on nonzero separable complex Hilbert spaces carrying regular irreducible finite-mode Weyl representations. Use $\hbar=1$, interleaved quadratures, $\Delta=\bigoplus_j\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$, and the Weyl phase $\exp(-iz^{\mathsf T}\Delta w/2)$. Write $K:Z_B\to Z_A$ and $\alpha$ for its real coupling and symmetric noise, with $\alpha\pm i(\Delta_B-K^{\mathsf T}\Delta_AK)/2\succeq0$. States below are normalized positive trace-class operators, without a Fock cutoff. All entropies and capacities use natural logarithms.
--
--   Specialize to two input modes and one output mode, with $K$ having interleaved rows $(1,0),(0,0),(0,1),(0,0)$ and vacuum noise $\alpha=I_2/2$. For $E>0$, impose $\operatorname{Tr}\rho(q_1^2+q_2^2)/2\le E$. Equivalently the classical signal has mean squared norm at most $2E$. Writing $g(x)=(x+1)\log(x+1)-x\log x$ for $x\ge0$, with $g(0)=0$, the constrained capacities satisfy
--
--   $$C_{\mathrm{ea}}(E)=C(E)=g(E).$$
--
--   Both capacities are the unrestricted constrained block capacities. This is the two-dimensional minimal-noise signal example; $E$ is the variance of each component in its optimal centered Gaussian modulation.
-- source:
--   Gaussian classical-quantum channels: gain of entanglement-assistance, arXiv:1211.4774v1, PDF p. 12, §4.1, explicit main result (30): two-dimensional minimal-noise signal

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

/-- Holevo arXiv:1211.4774v1, PDF pp.11-12, (30): two-dimensional vacuum signal.
The quantum cost is (q1^2+q2^2)/2, retaining the source factor one-half. -/
theorem two_dimensional_minimal_noise_capacity {I J : Type}
    [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (WA : ScaledWeylRepresentation I 2 1) (WB : ScaledWeylRepresentation J 1 1)
    (Phi : DualChannel I J)
    (hG : GaussianChannel WA WB Phi kTwo ((1 / 2 : ℝ) • 1))
    (E : ℝ) (hE : 0 < E) :
    (quadraticObservable WA kTwo ((1 / 2 : ℝ) • 1)).form =
      quadraticRaw WA kTwo ((1 / 2 : ℝ) • 1) ∧
    operationalAssistedCapacity Phi.predual.val
      (quadraticObservable WA kTwo ((1 / 2 : ℝ) • 1)) E =
      regularizedUnassistedCapacity Phi.predual.val
        (quadraticObservable WA kTwo ((1 / 2 : ℝ) • 1)) E ∧
    regularizedUnassistedCapacity Phi.predual.val
      (quadraticObservable WA kTwo ((1 / 2 : ℝ) • 1)) E = ENNReal.ofReal (g E) := by sorry

end QAlgorithms.Papers.Independent.Next46.P18

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_one_mode_gaussian_information
-- name    : QAlgorithms.Papers.Independent.Next46.P18.one_mode_gaussian_information
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:15:52.525628+00:00
-- url     : https://prove2.me/theorems/ab67cbeb-881a-4206-ac33-1a68fe7536d9
-- title:
--   §4.2, Gaussian-input mutual information and limiting deficit
-- statement:
--   Let $\Phi$ be a centered Gaussian completely positive trace-preserving channel on nonzero separable complex Hilbert spaces carrying regular irreducible finite-mode Weyl representations. Use $\hbar=1$, interleaved quadratures, $\Delta=\bigoplus_j\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$, and the Weyl phase $\exp(-iz^{\mathsf T}\Delta w/2)$. Write $K:Z_B\to Z_A$ and $\alpha$ for its real coupling and symmetric noise, with $\alpha\pm i(\Delta_B-K^{\mathsf T}\Delta_AK)/2\succeq0$. States below are normalized positive trace-class operators, without a Fock cutoff. All entropies and capacities use natural logarithms.
--
--   For the Example 2 channel $K=\operatorname{diag}(1,0)$, $\alpha=\operatorname{diag}(v,1/(4v))$, fix $E>0$ and $v=\sigma^2>0$. For $P\ge1/(4E)$ let $\rho$ be any centered Gaussian input with covariance $\operatorname{diag}(E,P)$. Define
--
--   $$A=g\!\left(\sqrt{\frac E{4v}+\frac14}-\frac12\right),\qquad \delta_1(P)=g\!\left(\sqrt{EP+\frac E{4v}}-\frac12\right)-g\!\left(\sqrt{EP}-\frac12\right).$$
--
--   Then $I(\rho,\Phi)$ is finite and
--
--   $$I(\rho,\Phi)=A-\delta_1(P).$$
--
--   The function $\delta_1$ is positive and strictly decreasing on $[1/(4E),\infty)$, equals $A$ at $P=1/(4E)$, and tends to zero as $P\to+\infty$. Here $g(x)=(x+1)\log(x+1)-x\log x$. This describes the actual Gaussian input family and its approach to the assisted value.
-- source:
--   Gaussian classical-quantum channels: gain of entanglement-assistance, arXiv:1211.4774v1, PDF p. 14, §4.2, Gaussian-input mutual information and limiting deficit

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

/-- Holevo arXiv:1211.4774v1, PDF pp.14-15: actual Gaussian-input information,
strictly positive decreasing deficit, its endpoint, and its limit. E and v are
fixed before P tends to infinity. No incorrect asymptotic constant is used. -/
theorem one_mode_gaussian_information {I J : Type}
    [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (WA : ScaledWeylRepresentation I 1 1) (WB : ScaledWeylRepresentation J 1 1)
    (Phi : DualChannel I J) (E v : ℝ) (hE : 0 < E) (hv : 0 < v)
    (hG : GaussianChannel WA WB Phi kOne (squeezedNoise v)) :
    (∀ (P : ℝ) (rho : State I), 1 / (4 * E) ≤ P →
      (∀ z, weylTraceCharacteristic WA rho.coefficients z =
        gaussianFunction 0 (diagonalCovariance 1 E P) z) →
      mutualInformation rho.coefficients Phi.predual.val < ⊤ ∧
      (mutualInformation rho.coefficients Phi.predual.val).toReal =
        g (Real.sqrt (E / (4 * v) + 1 / 4) - 1 / 2) - deltaOne E v P) ∧
    (∀ P : ℝ, 1 / (4 * E) ≤ P → 0 < deltaOne E v P) ∧
    StrictAntiOn (deltaOne E v) (Set.Ici (1 / (4 * E))) ∧
    deltaOne E v (1 / (4 * E)) = g (Real.sqrt (E / (4 * v) + 1 / 4) - 1 / 2) ∧
    Tendsto (deltaOne E v) atTop (𝓝 0) := by sorry

end QAlgorithms.Papers.Independent.Next46.P18

end

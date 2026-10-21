-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_one_mode_gaussian_mutual_information
-- name    : QAlgorithms.Papers.Independent.Next46.P18.one_mode_gaussian_mutual_information
-- status  : Open
-- author  : @Imine
-- created : 2026-10-21T01:36:17.524114+00:00
-- url     : https://prove2.me/theorems/adf7f194-b3c8-479c-b164-6c80fe7e0ff0
-- title:
--   Gaussian-input mutual information for the one-mode Example 2 channel
-- statement:
--   Let $\Phi$ be the one-mode Gaussian channel of Example 2, with coupling $K=\operatorname{diag}(1,0)$ and noise $\alpha=\operatorname{diag}(v,1/(4v))$, where $v>0$. Fix $E>0$ and $P\ge 1/(4E)$. Let $\rho$ be a centered Gaussian input state with covariance $\operatorname{diag}(E,P)$, expressed through its Weyl characteristic function,
--   $$
--   \operatorname{Tr}\!\left(\rho W_A(z)\right)=\exp\!\left(-\tfrac12 z^{\mathsf T}\operatorname{diag}(E,P)z\right).
--   $$
--   Write
--   $$
--   A=g\!\left(\sqrt{\frac{E}{4v}+\frac14}-\frac12\right),
--   \qquad
--   \delta_1(P)=g\!\left(\sqrt{EP+\frac{E}{4v}}-\frac12\right)-g\!\left(\sqrt{EP}-\frac12\right),
--   $$
--   with $g(x)=(x+1)\log(x+1)-x\log x$.
--
--   Then the quantum mutual information $I(\rho,\Phi)$ is finite and
--   $$
--   I(\rho,\Phi)=A-\delta_1(P).
--   $$
--   This is the Gaussian entropy computation that identifies the actual information available from the centered Gaussian family; it is the input-family formula behind the assisted-capacity value.
--
--   The Lean statement uses the platform definitions `mutualInformation`, `weylTraceCharacteristic`, `gaussianFunction`, and `diagonalCovariance`. The covariance hypothesis is stated through the characteristic function rather than through a separate Gaussian-state predicate.
-- source:
--   Holevo, Gaussian classical-quantum channels: gain of entanglement-assistance, arXiv:1211.4774v1, PDF pp.14-15, the Gaussian-input mutual-information computation for Example 2.

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

/-- PDF pp.14-15: the mutual information of a centered Gaussian input with
covariance `diag(E,P)` through the one-mode Example 2 channel. The formula is
the Gaussian entropy computation behind the limiting-deficit statement. -/
theorem one_mode_gaussian_mutual_information {I J : Type}
    [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (WA : ScaledWeylRepresentation I 1 1) (WB : ScaledWeylRepresentation J 1 1)
    (Phi : DualChannel I J) (E v : ℝ) (hE : 0 < E) (hv : 0 < v)
    (hG : GaussianChannel WA WB Phi kOne (squeezedNoise v)) :
    ∀ (P : ℝ) (rho : State I), 1 / (4 * E) ≤ P →
      (∀ z, weylTraceCharacteristic WA rho.coefficients z =
        gaussianFunction 0 (diagonalCovariance 1 E P) z) →
      mutualInformation rho.coefficients Phi.predual.val < ⊤ ∧
      (mutualInformation rho.coefficients Phi.predual.val).toReal =
        g (Real.sqrt (E / (4 * v) + 1 / 4) - 1 / 2) - deltaOne E v P := by sorry

end QAlgorithms.Papers.Independent.Next46.P18

end

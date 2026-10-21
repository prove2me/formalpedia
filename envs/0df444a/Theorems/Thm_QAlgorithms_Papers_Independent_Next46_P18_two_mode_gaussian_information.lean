-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_two_mode_gaussian_information
-- name    : QAlgorithms.Papers.Independent.Next46.P18.two_mode_gaussian_information
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:17:26.906779+00:00
-- url     : https://prove2.me/theorems/b577cb15-8879-48fa-8f5d-38b53e3a08ea
-- title:
--   §5.1, two-mode Gaussian mutual information and asymptotic approach
-- statement:
--   Let $\Phi$ be a centered Gaussian completely positive trace-preserving channel on nonzero separable complex Hilbert spaces carrying regular irreducible finite-mode Weyl representations. Use $\hbar=1$, interleaved quadratures, $\Delta=\bigoplus_j\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$, and the Weyl phase $\exp(-iz^{\mathsf T}\Delta w/2)$. Write $K:Z_B\to Z_A$ and $\alpha$ for its real coupling and symmetric noise, with $\alpha\pm i(\Delta_B-K^{\mathsf T}\Delta_AK)/2\succeq0$. States below are normalized positive trace-class operators, without a Fock cutoff. All entropies and capacities use natural logarithms.
--
--   For the two-input-mode vacuum-noise channel in Example 1, fix $E>0$. For $P\ge1/(4E)$ let $\rho_{12}$ be any centered Gaussian input with covariance $\operatorname{diag}(E,P,E,P)$. Put $\widetilde P=P+1/2+E/4$ and
--
--   $$\delta_2(P)=g\!\left(\sqrt E(\sqrt{\widetilde P}+\sqrt E/2)-1/2\right)+g\!\left(\sqrt E(\sqrt{\widetilde P}-\sqrt E/2)-1/2\right)-2g(\sqrt{EP}-1/2).$$
--
--   Then the quantum mutual information is finite and
--
--   $$I(\rho_{12},\Phi)=g(E)-\delta_2(P).$$
--
--   Here $g(x)=(x+1)\log(x+1)-x\log x$, $\delta_2(P)>0$ at every finite admissible $P$, $\delta_2(1/(4E))=g(E)$, and $\delta_2(P)\to0$ as $P\to+\infty$. Thus this family approaches $g(E)$ only asymptotically. No monotonicity or conclusion about other input states is inferred.
-- source:
--   Gaussian classical-quantum channels: gain of entanglement-assistance, arXiv:1211.4774v1, PDF p. 16, §5.1, two-mode Gaussian mutual information and asymptotic approach

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

/-- Holevo arXiv:1211.4774v1, PDF pp.16-17: two-mode Gaussian approach to g(E).
No monotonicity or global nonattainment is inferred from this Gaussian family. -/
theorem two_mode_gaussian_information {I J : Type}
    [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (WA : ScaledWeylRepresentation I 2 1) (WB : ScaledWeylRepresentation J 1 1)
    (Phi : DualChannel I J) (E : ℝ) (hE : 0 < E)
    (hG : GaussianChannel WA WB Phi kTwo ((1 / 2 : ℝ) • 1)) :
    (∀ (P : ℝ) (rho : State I), 1 / (4 * E) ≤ P →
      (∀ z, weylTraceCharacteristic WA rho.coefficients z =
        gaussianFunction 0 (diagonalCovariance 2 E P) z) →
      mutualInformation rho.coefficients Phi.predual.val < ⊤ ∧
      (mutualInformation rho.coefficients Phi.predual.val).toReal = g E - deltaTwo E P) ∧
    (∀ P : ℝ, 1 / (4 * E) ≤ P → 0 < deltaTwo E P) ∧
    deltaTwo E (1 / (4 * E)) = g E ∧ Tendsto (deltaTwo E) atTop (𝓝 0) := by sorry

end QAlgorithms.Papers.Independent.Next46.P18

end

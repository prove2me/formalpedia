-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_degenerate_constraints_nonattainment
-- name    : QAlgorithms.Papers.Independent.Next46.P18.degenerate_constraints_nonattainment
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:16:41.460751+00:00
-- url     : https://prove2.me/theorems/306d5453-7438-4444-b465-61707618ebbf
-- title:
--   §4, noncompact constraint sets and nonattainment assertions
-- statement:
--   Let $\Phi$ be a centered Gaussian completely positive trace-preserving channel on nonzero separable complex Hilbert spaces carrying regular irreducible finite-mode Weyl representations. Use $\hbar=1$, interleaved quadratures, $\Delta=\bigoplus_j\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$, and the Weyl phase $\exp(-iz^{\mathsf T}\Delta w/2)$. Write $K:Z_B\to Z_A$ and $\alpha$ for its real coupling and symmetric noise, with $\alpha\pm i(\Delta_B-K^{\mathsf T}\Delta_AK)/2\succeq0$. States below are normalized positive trace-class operators, without a Fock cutoff. All entropies and capacities use natural logarithms.
--
--   For Example 1 let the input have two modes, the output one mode, $K$ have rows $(1,0),(0,0),(0,1),(0,0)$, and $\alpha=(N+1/2)I_2$ with $N\ge0$; set $H_2=(q_1^2+q_2^2)/2$. For Example 2 take $K=\operatorname{diag}(1,0)$, $\alpha=\operatorname{diag}(v,1/(4v))$ with $v>0$, and $H_1=q_1^2$. For every $E>0$, define $\mathcal S_E^{(j)}=\{\rho:\operatorname{Tr}\rho H_j\le E\}$. In both examples,
--
--   $$\mathcal S_E^{(j)}\text{ is not compact in trace norm},\qquad I(\rho,\Phi_j)<\sup_{\sigma\in\mathcal S_E^{(j)}}I(\sigma,\Phi_j)\quad(\rho\in\mathcal S_E^{(j)}).$$
--
--   All normal states are included, including feasible states of infinite input entropy. This records noncompactness and global nonattainment, separately from the Gaussian approximating families.
-- source:
--   Gaussian classical-quantum channels: gain of entanglement-assistance, arXiv:1211.4774v1, PDF p. 11, §4, noncompact constraint sets and nonattainment assertions

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

/-- Holevo arXiv:1211.4774v1, PDF pp.11-13: both noncompact feasible sets and
nonattainment over ALL normal input states. Example 1 includes N>=0. The p.13
reference to (29) is read as (36), the Example 2 information supremum. -/
theorem degenerate_constraints_nonattainment {I J A B : Type}
    [Countable I] [Countable J] [Countable A] [Countable B]
    [Nonempty I] [Nonempty J] [Nonempty A] [Nonempty B]
    (WA : ScaledWeylRepresentation I 2 1) (WB : ScaledWeylRepresentation J 1 1)
    (WC : ScaledWeylRepresentation A 1 1) (WD : ScaledWeylRepresentation B 1 1)
    (Phi : DualChannel I J) (Psi : DualChannel A B)
    (N E v : ℝ) (hN : 0 ≤ N) (hE : 0 < E) (hv : 0 < v)
    (hPhi : GaussianChannel WA WB Phi kTwo ((N + 1 / 2) • 1))
    (hPsi : GaussianChannel WC WD Psi kOne (squeezedNoise v)) :
    (quadraticObservable WA kTwo ((1 / 2 : ℝ) • 1)).form =
      quadraticRaw WA kTwo ((1 / 2 : ℝ) • 1) ∧
    (quadraticObservable WC kOne 1).form = quadraticRaw WC kOne 1 ∧
    ¬ IsCompact (feasibleStates (quadraticObservable WA kTwo ((1 / 2 : ℝ) • 1)) E) ∧
    ¬ IsCompact (feasibleStates (quadraticObservable WC kOne 1) E) ∧
    (∀ rho ∈ feasibleStates (quadraticObservable WA kTwo ((1 / 2 : ℝ) • 1)) E,
      mutualInformation rho.coefficients Phi.predual.val <
        informationSupremum Phi.predual.val (quadraticObservable WA kTwo ((1 / 2 : ℝ) • 1)) E) ∧
    (∀ rho ∈ feasibleStates (quadraticObservable WC kOne 1) E,
      mutualInformation rho.coefficients Psi.predual.val <
        informationSupremum Psi.predual.val (quadraticObservable WC kOne 1) E) := by sorry

end QAlgorithms.Papers.Independent.Next46.P18

end

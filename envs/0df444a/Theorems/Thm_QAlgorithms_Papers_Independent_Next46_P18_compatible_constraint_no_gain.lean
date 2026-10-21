-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_compatible_constraint_no_gain
-- name    : QAlgorithms.Papers.Independent.Next46.P18.compatible_constraint_no_gain
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:13:01.886172+00:00
-- url     : https://prove2.me/theorems/53db7ab6-22ba-4055-8606-59a38230759a
-- title:
--   Proposition 2: no gain under the compatible quadratic constraint
-- statement:
--   Let $\Phi$ be a centered Gaussian completely positive trace-preserving channel on nonzero separable complex Hilbert spaces carrying regular irreducible finite-mode Weyl representations. Use $\hbar=1$, interleaved quadratures, $\Delta=\bigoplus_j\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$, and the Weyl phase $\exp(-iz^{\mathsf T}\Delta w/2)$. Write $K:Z_B\to Z_A$ and $\alpha$ for its real coupling and symmetric noise, with $\alpha\pm i(\Delta_B-K^{\mathsf T}\Delta_AK)/2\succeq0$. States below are normalized positive trace-class operators, without a Fock cutoff. All entropies and capacities use natural logarithms.
--
--   Assume that $\Phi$ is classical-quantum, that $\alpha$ is a minimal physical noise covariance, and that $K^{\mathsf T}$ is surjective onto $Z_B$. Let $\epsilon$ be a real symmetric strictly positive definite matrix on $Z_B$ and let $E>0$. Define the positive self-adjoint quadratic-form observable $H=R_AK\epsilon K^{\mathsf T}R_A^{\mathsf T}$ and its extended expectation. Let $C(E)$ and $C_{\mathrm{ea}}(E)$ be the unassisted and entanglement-assisted constrained block capacities, respectively. Then
--
--   $$C(E)=C_{\mathrm{ea}}(E)=\sup_{\rho:\operatorname{Tr}\rho H\le E}S(\Phi(\rho)).$$
--
--   The capacities retain arbitrary collective decoding and, for the assisted capacity, arbitrary shared entanglement. This identifies both capacities with the full feasible output-entropy supremum. No compactness or Gibbs-trace condition is imposed.
-- source:
--   Gaussian classical-quantum channels: gain of entanglement-assistance, arXiv:1211.4774v1, PDF p. 7, Proposition 2: no gain under the compatible quadratic constraint

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

/-- Holevo arXiv:1211.4774v1, PDF pp.6-9, Proposition 2, (19).
E>0 is the regime of the source's division-by-E proof. The full-rank condition
is surjectivity of K transpose, not of K. Both capacity equalities are retained. -/
theorem compatible_constraint_no_gain {I J : Type} [Countable I] [Countable J]
    [Nonempty I] [Nonempty J] {s t : ℕ}
    (WA : ScaledWeylRepresentation I s 1) (WB : ScaledWeylRepresentation J t 1)
    (Phi : DualChannel I J) (K : Matrix (QuadratureIndex s) (QuadratureIndex t) ℝ)
    (alpha : Matrix (QuadratureIndex t) (QuadratureIndex t) ℝ) (hG : GaussianChannel WA WB Phi K alpha)
    (hcq : IsCQ Phi) (hminimal : MinimalNoise alpha)
    (hrank : Function.Surjective K.transpose.mulVec)
    (epsilon : Matrix (QuadratureIndex t) (QuadratureIndex t) ℝ) (hepsilon : epsilon.PosDef)
    (E : ℝ) (hE : 0 < E) :
    (quadraticObservable WA K epsilon).form = quadraticRaw WA K epsilon ∧
    regularizedUnassistedCapacity Phi.predual.val (quadraticObservable WA K epsilon) E =
      operationalAssistedCapacity Phi.predual.val (quadraticObservable WA K epsilon) E ∧
    operationalAssistedCapacity Phi.predual.val (quadraticObservable WA K epsilon) E =
      ⨆ rho : {rho : State I // rho ∈ feasibleStates (quadraticObservable WA K epsilon) E},
        homogeneousEntropy (Phi.predual.val rho.val.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Next46.P18

end

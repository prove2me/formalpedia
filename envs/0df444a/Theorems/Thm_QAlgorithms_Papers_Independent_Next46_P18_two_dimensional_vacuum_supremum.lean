-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_two_dimensional_vacuum_supremum
-- name    : QAlgorithms.Papers.Independent.Next46.P18.two_dimensional_vacuum_supremum
-- status  : Open
-- author  : @Imine
-- created : 2026-10-21T02:52:26.644251+00:00
-- url     : https://prove2.me/theorems/4ce92ef0-fc67-49ed-be5d-500ae48b4bbf
-- title:
--   Gaussian entropy supremum for the two-dimensional vacuum signal
-- statement:
--   Let $\Phi$ be a Gaussian channel with two input modes and one output mode, coupling
--   $$
--   K=\begin{pmatrix}1&0\\0&0\\0&1\\0&0\end{pmatrix}
--   $$
--   in interleaved coordinates, and vacuum noise $\alpha=\frac12\mathbf 1_2$. Let
--   $$
--   H=\frac{q_1^2+q_2^2}{2}
--   $$
--   and, for $E>0$, let $\mathcal S_E=\{\rho:\operatorname{Tr}\rho H\le E\}$ be the feasible set of normal input states. Write $g(x)=(x+1)\log(x+1)-x\log x$.
--
--   Then
--   $$
--   \sup_{\rho\in\mathcal S_E}S(\Phi(\rho))=g(E).
--   $$
--   The supremum is over all normal states, including states of infinite input entropy; the value is attained in the Gaussian family but the statement itself is only the supremum identity. This is the Gaussian optimization that evaluates the constrained output entropy in the two-dimensional minimal-noise example.
-- source:
--   Holevo, Gaussian classical-quantum channels: gain of entanglement-assistance, arXiv:1211.4774v1, PDF pp.11-12, the Gaussian optimization behind (30).

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

/-- For the two-mode vacuum signal with cost `(q1^2+q2^2)/2`, the supremum
of the output entropy over the feasible input states is `g(E)`. -/
theorem two_dimensional_vacuum_supremum {I J : Type}
    [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (WA : ScaledWeylRepresentation I 2 1) (WB : ScaledWeylRepresentation J 1 1)
    (Phi : DualChannel I J)
    (hG : GaussianChannel WA WB Phi kTwo ((1 / 2 : ℝ) • 1))
    (E : ℝ) (hE : 0 < E) :
    (⨆ rho : {rho : State I //
        rho ∈ feasibleStates (quadraticObservable WA kTwo ((1 / 2 : ℝ) • 1)) E},
      homogeneousEntropy (Phi.predual.val rho.val.coefficients)) =
      ENNReal.ofReal (g E) := by sorry

end QAlgorithms.Papers.Independent.Next46.P18

end

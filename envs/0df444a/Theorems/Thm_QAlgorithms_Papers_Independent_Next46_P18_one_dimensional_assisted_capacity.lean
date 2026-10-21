-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_one_dimensional_assisted_capacity
-- name    : QAlgorithms.Papers.Independent.Next46.P18.one_dimensional_assisted_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:15:09.801977+00:00
-- url     : https://prove2.me/theorems/43fdd3d2-22d2-469a-ae39-435fee6c6acd
-- title:
--   §4.2, explicit entanglement-assisted capacity formula
-- statement:
--   Let $\Phi$ be a centered Gaussian completely positive trace-preserving channel on nonzero separable complex Hilbert spaces carrying regular irreducible finite-mode Weyl representations. Use $\hbar=1$, interleaved quadratures, $\Delta=\bigoplus_j\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)$, and the Weyl phase $\exp(-iz^{\mathsf T}\Delta w/2)$. Write $K:Z_B\to Z_A$ and $\alpha$ for its real coupling and symmetric noise, with $\alpha\pm i(\Delta_B-K^{\mathsf T}\Delta_AK)/2\succeq0$. States below are normalized positive trace-class operators, without a Fock cutoff. All entropies and capacities use natural logarithms.
--
--   Specialize to one input and one output mode with $K=\operatorname{diag}(1,0)$ and $\alpha=\operatorname{diag}(v,1/(4v))$, where $v=\sigma^2>0$. For $E>0$, impose only $\operatorname{Tr}\rho q_1^2\le E$, with no restriction on momentum variance. Then
--
--   $$C_{\mathrm{ea}}(E)=g\!\left(\sqrt{\frac E{4v}+\frac14}-\frac12\right)=g\!\left(\frac{\sqrt{1+E/v}-1}{2}\right),$$
--
--   where $g(x)=(x+1)\log(x+1)-x\log x$. This evaluates the assisted capacity independently of the erroneous unassisted formula (33). Finite Gaussian inputs can approach the supremum; attainment is not assumed.
-- source:
--   Gaussian classical-quantum channels: gain of entanglement-assistance, arXiv:1211.4774v1, PDF p. 15, §4.2, explicit entanglement-assisted capacity formula

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

/-- Holevo arXiv:1211.4774v1, PDF pp.14-15: assisted capacity of Example 2.
The cost q1^2 imposes no finite momentum or input-entropy hypothesis. This
formula does not endorse the erroneous unassisted capacity (33). -/
theorem one_dimensional_assisted_capacity {I J : Type}
    [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (WA : ScaledWeylRepresentation I 1 1) (WB : ScaledWeylRepresentation J 1 1)
    (Phi : DualChannel I J) (E v : ℝ) (hE : 0 < E) (hv : 0 < v)
    (hG : GaussianChannel WA WB Phi kOne (squeezedNoise v)) :
    (quadraticObservable WA kOne 1).form = quadraticRaw WA kOne 1 ∧
    operationalAssistedCapacity Phi.predual.val (quadraticObservable WA kOne 1) E =
      ENNReal.ofReal (g (Real.sqrt (E / (4 * v) + 1 / 4) - 1 / 2)) ∧
    g (Real.sqrt (E / (4 * v) + 1 / 4) - 1 / 2) =
      g ((Real.sqrt (1 + E / v) - 1) / 2) := by sorry

end QAlgorithms.Papers.Independent.Next46.P18

end

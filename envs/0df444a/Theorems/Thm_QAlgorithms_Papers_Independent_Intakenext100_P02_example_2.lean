-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_example_2
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.example_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:47:42.718361+00:00
-- url     : https://prove2.me/theorems/36d5f496-732e-4880-a0dd-a97a984a705c
-- title:
--   Example 2: dephasing saturates the discord-based lower bound
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   For basis dephasing $\Phi$ in any complete basis of a finite $d$-dimensional system, $d\ge1$, the channel complements itself. The maximally entangled input formed from that basis and any reference basis has q-c output, hence
--
--   $$\varepsilon_\Phi=0,\qquad\overline C(\Phi)=\ln d=(1-\varepsilon_\Phi)\ln d-g(\varepsilon_\Phi).$$
--   The formalization constructs the maximally entangled coefficients and asserts normalized purity, rather than assuming an unrelated q-c output. This is an equality witness for the capacity lower bound.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 42, Example 2: dephasing saturates the discord-based lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P02

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Intakenext100.P02

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsTraceClass traceSize rankOne productCoeff tensorApply)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (Channel Complementary Purifies traceFirst traceSecond mutualInformation
   barycentricChi CountableStateEnsemble Barycenter convexOperatorMixture channelTensorAction)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble HasAverage HasFiniteSupport averageCoefficients
   extendedEntropyNats extendedRelativeEntropyNats ensembleHolevo pureStates)

open QAlgorithms.Papers.Independent.Frontier18.P08
  (IsQuantumOperation operatorTrace StronglyConverges TraceNormConverges)

open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator conjugateCoeff)

open QAlgorithms.Papers.Independent.Gap48.P45
  (boundedTracePair dimensionCount generatedSpace outputSpace coefficientTraceHasSum)

open QAlgorithms.Papers.Independent.Renew46.P08 (qmi)

open QAlgorithms.Papers.Independent.Claimed50.P18 (swapCoeff associateRight dropMiddle)

open QAlgorithms.Papers.Independent.Frontier18.P01 (binaryEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:2304.05388v3, Example 2, PDF p.42. Every finite basis, including d=1. -/
theorem example_2 {A : Type} [Fintype A] [Nonempty A]
    (b c : HilbertBasis A ℂ (Hilbert A)) :
    (∃ Phi : Channel A A, (∀ X, IsTraceClass X → Phi.val X = basisDephasingCoefficients b X) ∧ Complementary Phi Phi) ∧
    (∃ psi : PureState (A × A), psi.val.coefficients = entangledCoeff b c ∧
      MaximallyEntangled psi ∧ UniformQC (tensorApply (basisDephasingCoefficients b) psi.val.coefficients)) ∧
    qcProximity (basisDephasingCoefficients b) = 0 ∧
    generalizedHolevoCapacity (basisDephasingCoefficients b) = ENNReal.ofReal (Real.log (Fintype.card A)) ∧
    (1 - qcProximity (basisDephasingCoefficients b)) * Real.log (Fintype.card A) - correctionG (qcProximity (basisDephasingCoefficients b)) =
      (generalizedHolevoCapacity (basisDephasingCoefficients b)).toReal := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

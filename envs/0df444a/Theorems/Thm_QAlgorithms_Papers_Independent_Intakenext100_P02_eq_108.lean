-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_eq_108
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.eq_108
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:43:27.749585+00:00
-- url     : https://prove2.me/theorems/0118f183-58bb-4c6c-bf3f-a83ed95dd906
-- title:
--   Constrained discord deficit under concatenation (108)
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   For $\overline C(\Phi,\rho)<\infty$, define $\Delta(\Phi,\rho)=I(\Phi,\rho)-\overline C(\Phi,\rho)$. Then for every channel $\Psi$ composable with $\Phi$,
--
--   $$\Delta(\Psi\circ\Phi,\rho)\le\Delta(\Phi,\rho).$$
--   Both deficits may be infinite. This is monotonicity of the constrained discord deficit under concatenation.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 40, Constrained discord deficit under concatenation (108)

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

/-- arXiv:2304.05388v3, (108), PDF p.40. No finite-MI hypothesis. -/
theorem eq_108 {A B C : Type} [Countable A] [Countable B] [Countable C]
    [Nonempty A] [Nonempty B] [Nonempty C] (Phi : Channel A B) (Psi : Channel B C)
    (rho : State A) (hfinite : barycentricChi rho.coefficients Phi.val < ⊤) :
    constrainedInformationDeficit (Psi.val ∘ Phi.val) rho.coefficients ≤ constrainedInformationDeficit Phi.val rho.coefficients := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

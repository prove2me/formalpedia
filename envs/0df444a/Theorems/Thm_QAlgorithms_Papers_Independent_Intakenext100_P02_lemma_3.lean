-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_lemma_3
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.lemma_3
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:25:22.960987+00:00
-- url     : https://prove2.me/theorems/484f2a67-a3fe-47ed-b264-2d7ce080ace0
-- title:
--   Lemma 3: discord under a trace-nonincreasing operation
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   Let $C_B(\omega)<\infty$ and let $\Phi$ be a completely positive trace-nonincreasing complex-linear operation on $A$, with arbitrary separable output. Its actual success probability is $c=\operatorname{Tr}\Phi(\omega_A)>0$. Then
--
--   $$cD_B\!\left((\Phi\otimes\mathrm{Id}_B)(\omega)/c\right)\le D_B(\omega).$$
--   Discord may be infinite. This gives the postselection monotonicity bound without postulating a separate success law.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 20, Lemma 3: discord under a trace-nonincreasing operation

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

/-- arXiv:2304.05388v3, Lemma 3, PDF p.20. Success probability is computed. -/
theorem lemma_3 {A B D : Type} [Countable A] [Countable B] [Countable D]
    [Nonempty A] [Nonempty B] [Nonempty D] (omega : State (A × B))
    (Phi : Matrix A A ℂ → Matrix D D ℂ) (hPhi : IsQuantumOperation Phi)
    (hdomain : discreteClassicalCorrelation omega.coefficients < ⊤)
    (hc : 0 < operatorTrace (Phi (traceSecond omega.coefficients))) :
    ENNReal.ofReal (operatorTrace (Phi (traceSecond omega.coefficients))) *
      discreteOptimizedDiscord (((operatorTrace (Phi (traceSecond omega.coefficients)))⁻¹ : ℂ) •
        tensorApply Phi omega.coefficients) ≤ discreteOptimizedDiscord omega.coefficients := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

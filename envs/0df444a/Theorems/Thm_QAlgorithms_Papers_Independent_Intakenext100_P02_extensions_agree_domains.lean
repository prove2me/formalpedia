-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_extensions_agree_domains
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.extensions_agree_domains
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:32:44.808773+00:00
-- url     : https://prove2.me/theorems/db9e332d-f5d3-4392-9d94-a34c884f3737
-- title:
--   Agreement domains of the two optimized extensions
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   For every state satisfying any one of the three alternatives $C_B(\omega)<\infty$, $S(\omega)<\infty$, or q-c structure,
--
--   $$\widehat D_B(\omega)=\widetilde D_B(\omega).$$
--   The q-c alternative includes infinite QMI. This records the established agreement domains without asserting the global conjecture.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 26, Agreement domains of the two optimized extensions

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

/-- arXiv:2304.05388v3, agreement domains, PDF p.26. Three alternatives. -/
theorem extensions_agree_domains {A B : Type} [Countable A] [Countable B]
    [Nonempty A] [Nonempty B] (omega : State (A × B))
    (h : discreteClassicalCorrelation omega.coefficients < ⊤ ∨ extendedEntropyNats omega.coefficients < ⊤ ∨
      IsQC omega.coefficients) : infDiscord omega.coefficients = supDiscord omega.coefficients := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

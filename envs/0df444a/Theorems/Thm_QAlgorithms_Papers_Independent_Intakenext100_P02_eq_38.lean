-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_eq_38
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.eq_38
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:17:17.215329+00:00
-- url     : https://prove2.me/theorems/f13af8c1-bbbc-47a1-81a4-5982514bac1b
-- title:
--   Generalized Koashi–Winter relation (38)
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   For every normalized pure tripartite state $\omega_{ABC}$, with no marginal entropy finiteness condition,
--
--   $$C_B(\omega_{AB})=\chi_A(\omega_{AC}).$$
--   Here $\chi_A$ is the constrained Holevo capacity of partial trace from $AC$ to $A$, optimized over all discrete ensembles of exact average $\omega_{AC}$. Both sides may be infinite. This is the generalized Koashi–Winter identity.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 15, Generalized Koashi–Winter relation (38)

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

/-- arXiv:2304.05388v3, generalized Koashi–Winter relation (38), PDF p.15. -/
theorem eq_38 {A B C : Type} [Countable A] [Countable B] [Countable C]
    [Nonempty A] [Nonempty B] [Nonempty C] (omega : PureState ((A × B) × C)) :
    discreteClassicalCorrelation (traceSecond omega.val.coefficients) = chiA (tripartiteAC omega.val.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

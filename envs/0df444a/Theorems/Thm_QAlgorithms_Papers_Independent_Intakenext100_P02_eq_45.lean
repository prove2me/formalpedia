-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_eq_45
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.eq_45
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:21:55.194883+00:00
-- url     : https://prove2.me/theorems/fc00bf31-a408-4e0b-bc77-c6cb5a445cd6
-- title:
--   Generalized Xi–Lu–Wang–Li relation (45)
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   For every normalized pure $\omega_{ABC}$,
--
--   $$C_B(\omega_{AB})=\sup_{M\in\mathcal M_B}\mathrm{ER}(\omega_{BC},M\otimes I_C)=\sup_{M\in\mathcal M_B^0}\mathrm{ER}(\omega_{BC},M\otimes I_C).$$
--   Here $\mathcal M_B$ comprises all discrete POVMs and $\mathcal M_B^0$ the rank-one ones. Zero effects may be deleted. These are suprema and may be infinite; no maximizing measurement is asserted.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 16, Generalized Xi–Lu–Wang–Li relation (45)

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

/-- arXiv:2304.05388v3, generalized relation (45), PDF pp.16–17. -/
theorem eq_45 {A B C : Type} [Countable A] [Countable B] [Countable C]
    [Nonempty A] [Nonempty B] [Nonempty C] (omega : PureState ((A × B) × C)) :
    discreteClassicalCorrelation (traceSecond omega.val.coefficients) =
      (⨆ (K : Type) (_ : Countable K) (M : DiscretePOVM B K), firstER M (traceA omega.val.coefficients)) ∧
    discreteClassicalCorrelation (traceSecond omega.val.coefficients) =
      (⨆ (K : Type) (_ : Countable K) (M : {M : DiscretePOVM B K // HasRankOneEffects M}),
        firstER M.val (traceA omega.val.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

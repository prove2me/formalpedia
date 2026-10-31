-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_eq_41_infinite
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.eq_41_infinite
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:20:10.498419+00:00
-- url     : https://prove2.me/theorems/d68dbf6f-6722-403c-a658-5d61e08866bc
-- title:
--   Finite-measured-entropy Xi–Lu–Wang–Li relation
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   For every normalized pure $\omega_{ABC}$ with $S(\omega_B)<\infty$,
--
--   $$C_B(\omega_{AB})+D_B(\omega_{BC})=S(\omega_B).$$
--   The discord of $BC$ measures the first subsystem $B$; the formalization swaps tensor coordinates to preserve this ownership. This extends the Xi–Lu–Wang–Li identity beyond finite systems.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 15, Finite-measured-entropy Xi–Lu–Wang–Li relation

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

/-- arXiv:2304.05388v3, infinite-system extension of (41), PDF pp.15–16. -/
theorem eq_41_infinite {A B C : Type} [Countable A] [Countable B] [Countable C]
    [Nonempty A] [Nonempty B] [Nonempty C] (omega : PureState ((A × B) × C))
    (hfinite : extendedEntropyNats (traceFirst (traceSecond omega.val.coefficients)) < ⊤) :
    discreteClassicalCorrelation (traceSecond omega.val.coefficients) + discreteOptimizedDiscord (swapCoeff (traceA omega.val.coefficients)) =
      extendedEntropyNats (traceFirst (traceSecond omega.val.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

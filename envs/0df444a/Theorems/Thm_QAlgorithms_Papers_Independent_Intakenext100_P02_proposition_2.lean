-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_proposition_2
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.proposition_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:23:15.600402+00:00
-- url     : https://prove2.me/theorems/4ddb2291-313c-40e4-a7d4-e24e8bd70154
-- title:
--   Proposition 2A–B: discord lower semicontinuity
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   For every fixed discrete POVM $M$, the unoptimized discord is lower semicontinuous on $C_B^M<\infty$, and optimized discord is lower semicontinuous on $C_B<\infty$:
--
--   $$D_B^M=I(A:B)-C_B^M,\qquad D_B=I(A:B)-C_B.$$
--   The QMI may be infinite. These are the natural finite-subtrahend domains, with no energy constraint.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 17, Proposition 2A–B: discord lower semicontinuity

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

/-- arXiv:2304.05388v3, Proposition 2A–B, PDF pp.17–18. -/
theorem proposition_2 {A B K : Type} [Countable A] [Countable B]
    [Nonempty A] [Nonempty B] [Countable K] (M : DiscretePOVM B K) :
    LowerSemicontinuousOn (fun omega : State (A × B) => discordM M omega.coefficients)
      {omega | classicalM M omega.coefficients < ⊤} ∧
    LowerSemicontinuousOn (fun omega : State (A × B) => discreteOptimizedDiscord omega.coefficients)
      {omega | discreteClassicalCorrelation omega.coefficients < ⊤} := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

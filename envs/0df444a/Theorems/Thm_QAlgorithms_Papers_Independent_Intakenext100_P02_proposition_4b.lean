-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_proposition_4b
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.proposition_4b
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:27:31.24744+00:00
-- url     : https://prove2.me/theorems/6d5758b8-5a93-4b1a-ae7b-f6f069cf3285
-- title:
--   Proposition 4B)
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   Fix a complete orthonormal basis $\{|i\rangle\}$ of $B$ and its matching projective measurement $M$. Every q-c state diagonal in that same basis satisfies
--
--   $$\widehat D_B^M(\omega)=0.$$
--   The total and marginal entropies and QMI may be infinite. This concerns one specified basis, not an arbitrary fixed measurement after changing the state basis.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 21, Proposition 4B)

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

/-- arXiv:2304.05388v3, Proposition 4B, PDF pp.21–23. Same basis in the state
and the measurement, with no entropy or QMI finiteness premise. -/
theorem proposition_4b {A B : Type} [Countable A] [Countable B]
    [Nonempty A] [Nonempty B] (b : HilbertBasis B ℂ (Hilbert B))
    (M : DiscretePOVM B B) (hM : ∀ i v, M.effect i v = (inner ℂ (b i) v) • b i)
    (omega : State (A × B)) (hqc : QCInBasis b omega.coefficients) :
    extendedDiscordM M omega.coefficients = 0 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

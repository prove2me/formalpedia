-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_lemma_7
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.lemma_7
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:53:55.201398+00:00
-- url     : https://prove2.me/theorems/90cf8b1a-135e-443f-9328-043b83aceed3
-- title:
--   Lemma 7: compactness of finite orthogonal projector tuples
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   Fix a finite $m\ge0$. Let $\{P_i^{(n)}\}_{i=1}^m$ be mutually orthogonal rank-one projectors and suppose their sum tends in trace norm to a rank-$m$ orthogonal projection $Q$. Then there are mutually orthogonal rank-one $P_i^{(0)}$ and a single strictly increasing subsequence $n_k$ such that
--
--   $$P_i^{(n_k)}\to P_i^{(0)}\quad(1\le i\le m),\qquad\sum_{i=1}^mP_i^{(0)}=Q.$$
--   For $m=0$ the tuple is empty and $Q=0$. This is compactness after subsequence selection, not convergence of the original tuples.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 47, Lemma 7: compactness of finite orthogonal projector tuples

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

/-- arXiv:2304.05388v3, Lemma 7, PDF p.47. m=0 is allowed. -/
theorem lemma_7 {I : Type} [Countable I] [Nonempty I] (m : ℕ)
    (P : ℕ → Fin m → Matrix I I ℂ) (Q : Matrix I I ℂ)
    (hP : ∀ n, OrthogonalTuple (P n)) (hQ : RankMProjection m Q)
    (hconv : TraceNormConverges (fun n => ∑ i, P n i) Q) :
    ∃ (P0 : Fin m → Matrix I I ℂ) (k : ℕ → ℕ), OrthogonalTuple P0 ∧
      StrictMono k ∧ (∀ i, TraceNormConverges (fun n => P (k n) i) (P0 i)) ∧
      (∑ i, P0 i) = Q := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

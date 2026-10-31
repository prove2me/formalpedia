-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_lemma_6
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.lemma_6
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:52:47.276986+00:00
-- url     : https://prove2.me/theorems/acef5de1-20e6-49c5-89ae-e3fbe4ba13d9
-- title:
--   Lemma 6: subsequential convergence of weighted spectral projectors
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   Let $\rho_n\to\rho_0$ in trace norm, and fix for each $n$ a rank-one spectral decomposition with eigenvalues $\lambda_i^{(n)}$ in nonincreasing order. There are a spectral decomposition of $\rho_0$ and one strictly increasing subsequence $n_k$ such that
--
--   $$\lambda_i^{(n_k)}P_i^{(n_k)}\longrightarrow\lambda_i^{(0)}P_i^{(0)}\quad\text{in trace norm for every }i.$$
--   Finite spectral supports are represented by zero terms. No convergence of bare projectors at a zero limiting eigenvalue is asserted. This is simultaneous subsequential convergence of weighted spectral projectors.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 46, Lemma 6: subsequential convergence of weighted spectral projectors

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

/-- arXiv:2304.05388v3, Lemma 6, PDF pp.46–47. One common subsequence for
EVERY weighted eigenprojector. Finite support uses zero terms, not infinitely
many orthogonal unit vectors in a finite-dimensional space. -/
theorem lemma_6 {I : Type} [Countable I] [Nonempty I]
    (rho : ℕ → State I) (rho0 : State I) (hconv : Tendsto rho atTop (𝓝 rho0))
    (spectral : ∀ n, SpectralExpansion (rho n)) :
    ∃ (spectral0 : SpectralExpansion rho0) (k : ℕ → ℕ), StrictMono k ∧
      ∀ i, TraceNormConverges (fun n => (spectral (k n)).term i) (spectral0.term i) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

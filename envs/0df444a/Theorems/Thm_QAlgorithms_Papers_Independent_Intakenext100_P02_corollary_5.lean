-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_corollary_5
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.corollary_5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:23:56.790891+00:00
-- url     : https://prove2.me/theorems/cef972a7-b1be-4a6b-a020-5e6a74eae7e1
-- title:
--   Corollary 5: convergence of quantum and classical correlations
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   If $\omega_n\to\omega_0$ and $I(A:B)_{\omega_n}\to I(A:B)_{\omega_0}<\infty$, then, for every fixed discrete $M$,
--
--   $$f(\omega_n)\longrightarrow f(\omega_0)<\infty,\qquad f\in\{C_B,D_B,C_B^M,D_B^M\}.$$
--   Thus finite continuity of the total correlation implies continuity of all four stated correlation quantities.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 18, Corollary 5: convergence of quantum and classical correlations

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

/-- arXiv:2304.05388v3, Corollary 5, PDF pp.18–19. -/
theorem corollary_5 {A B K : Type} [Countable A] [Countable B]
    [Nonempty A] [Nonempty B] [Countable K] (M : DiscretePOVM B K)
    (omega : ℕ → State (A × B)) (omega0 : State (A × B))
    (hconv : Tendsto omega atTop (𝓝 omega0))
    (hmi : Tendsto (fun n => qmi (omega n).coefficients) atTop (𝓝 (qmi omega0.coefficients)))
    (hfinite : qmi omega0.coefficients < ⊤) :
    (∀ f ∈ ({discreteClassicalCorrelation, discreteOptimizedDiscord, classicalM M, discordM M} :
        Set (Matrix (A × B) (A × B) ℂ → ℝ≥0∞)),
      Tendsto (fun n => f (omega n).coefficients) atTop (𝓝 (f omega0.coefficients)) ∧
        f omega0.coefficients < ⊤) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

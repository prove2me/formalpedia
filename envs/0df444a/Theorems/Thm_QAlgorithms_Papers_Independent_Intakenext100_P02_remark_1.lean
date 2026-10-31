-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_remark_1
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.remark_1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:11:20.195566+00:00
-- url     : https://prove2.me/theorems/96fcb627-859c-4e18-8379-f76ad348f579
-- title:
--   Remark 1: both entropy-reduction bounds are attained
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   Both entropy upper bounds have explicit attaining families. For every product state and rank-one POVM,
--
--   $$R_M(\rho\otimes\sigma)=S(\sigma)=S((\rho\otimes\sigma)_B).$$
--   For $\omega=\sum_i p_i\rho_i\otimes|i\rangle\langle i|$, where the $\rho_i$ are pure, the $p_i$ form a probability distribution and $\{|i\rangle\}$ is a complete orthonormal basis of $B$, the matching basis measurement gives $R_M(\omega)=H(p)=S(\omega)$. The Shannon entropy $H(p)=\sum_i-p_i\ln p_i$ may be infinite. These families establish attainment of both upper bounds.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 9, Remark 1: both entropy-reduction bounds are attained

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

/-- arXiv:2304.05388v3, Remark 1, PDF p.9. Both explicit attaining families. -/
theorem remark_1 {A B : Type} [Countable A] [Countable B] [Nonempty A] [Nonempty B] :
    (∀ (K : Type) [Countable K] (M : DiscretePOVM B K), HasRankOneEffects M →
      ∀ (rho : State A) (sigma : State B),
        localER M (productCoeff rho.coefficients sigma.coefficients) = extendedEntropyNats sigma.coefficients ∧
        extendedEntropyNats (traceFirst (productCoeff rho.coefficients sigma.coefficients)) =
          extendedEntropyNats sigma.coefficients) ∧
    (∀ (b : HilbertBasis B ℂ (Hilbert B)) (w : B → ℝ) (rho : B → State A)
      (M : DiscretePOVM B B), (∀ i, 0 ≤ w i) → HasSum w 1 →
      (∀ i, rho i ∈ pureStates A) →
      (∀ i v, M.effect i v = (inner ℂ (b i) v) • b i) →
      localER M (cqCoefficients b w rho) = indexShannonNats w ∧
        extendedEntropyNats (cqCoefficients b w rho) = indexShannonNats w) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

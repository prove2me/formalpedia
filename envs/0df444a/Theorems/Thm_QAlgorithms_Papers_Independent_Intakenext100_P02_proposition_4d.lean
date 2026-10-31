-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_proposition_4d
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.proposition_4d
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:28:18.967386+00:00
-- url     : https://prove2.me/theorems/742d4090-229a-44d9-9f40-70d254d5730c
-- title:
--   Proposition 4D)
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   For arbitrary states, $0\le p\le1$, and $\omega_p=p\rho+(1-p)\sigma$, put $a=p\widehat D_B^M(\rho)+(1-p)\widehat D_B^M(\sigma)$. Then
--
--   $$a\le\widehat D_B^M(\omega_p)+h_2(p),\qquad \widehat D_B^M(\omega_p)\le a+h_2(p).$$
--   Both inequalities allow infinite values; zero times infinity is zero. The additive lower form avoids subtracting infinities. These give the two almost-affinity bounds.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 21, Proposition 4D)

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

/-- arXiv:2304.05388v3, Proposition 4D, PDF pp.21–23. Both bounds, written
additively so infinity minus infinity never occurs. -/
theorem proposition_4d {A B K : Type} [Countable A] [Countable B]
    [Nonempty A] [Nonempty B] [Countable K] (M : DiscretePOVM B K)
    (rho sigma : State (A × B)) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ENNReal.ofReal p * extendedDiscordM M rho.coefficients +
      ENNReal.ofReal (1-p) * extendedDiscordM M sigma.coefficients ≤
        extendedDiscordM M (convexOperatorMixture p rho.coefficients sigma.coefficients) +
          binaryEntropy p ∧
    extendedDiscordM M (convexOperatorMixture p rho.coefficients sigma.coefficients) ≤
      ENNReal.ofReal p * extendedDiscordM M rho.coefficients +
        ENNReal.ofReal (1-p) * extendedDiscordM M sigma.coefficients +
          binaryEntropy p := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

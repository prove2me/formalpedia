-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_example_1
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.example_1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:42:42.553095+00:00
-- url     : https://prove2.me/theorems/60d8d38d-c15e-4ae0-86d7-34385176ba2b
-- title:
--   Example 1: semigroup comparison of information decreases
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   Let $\{\Phi_t\}_{t\ge0}$ be an algebraic channel semigroup and let $S(\overline\rho(\mu))<\infty$. Define $F(t)=I(\Phi_t,\overline\rho(\mu))$ and $G(t)=\chi(\Phi_t(\mu))$. Both functions are nonincreasing, $0\le G(t)\le F(t)<\infty$, and
--
--   $$0\le G(t)-G(t+s)\le F(t)-F(t+s)\qquad(t,s\ge0).$$
--   No continuity or differentiability in time is assumed. This compares finite information decreases, not derivatives.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 39, Example 1: semigroup comparison of information decreases

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

/-- arXiv:2304.05388v3, Example 1, PDF pp.39–40. Algebraic decreases, with
finite functions and no differentiability hypothesis or derivative conclusion. -/
theorem example_1 {A : Type} [Countable A] [Nonempty A]
    (Phi : TraceClassChannelSemigroup A) (mu : GeneralizedEnsemble A)
    (hfinite : extendedEntropyNats (averageCoefficients mu) < ⊤) :
    Antitone (fun t => mutualInformation (averageCoefficients mu) (Phi.channel t).val) ∧
    Antitone (fun t => ensembleHolevo (Phi.channel t).val mu) ∧
    (∀ t, ensembleHolevo (Phi.channel t).val mu ≤
      mutualInformation (averageCoefficients mu) (Phi.channel t).val ∧
      mutualInformation (averageCoefficients mu) (Phi.channel t).val < ⊤) ∧
    ∀ t s, ensembleHolevo (Phi.channel t).val mu - ensembleHolevo (Phi.channel (t+s)).val mu ≤
      mutualInformation (averageCoefficients mu) (Phi.channel t).val -
        mutualInformation (averageCoefficients mu) (Phi.channel (t+s)).val := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

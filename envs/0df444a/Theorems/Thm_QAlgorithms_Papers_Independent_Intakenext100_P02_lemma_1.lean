-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_lemma_1
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.lemma_1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:52:59.847676+00:00
-- url     : https://prove2.me/theorems/76a82d36-325d-4bca-90f3-f5a6b8bb9959
-- title:
--   Lemma 1: lower semicontinuity of the preprocessing mutual-information loss
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   For channels $\Phi:A\to B$ and $\Psi:B\to C$, the preprocessing loss is nonnegative and lower semicontinuous on precisely the states with $I(\Psi\circ\Phi,\rho)<\infty$:
--
--   $$L(\rho)=I(\Psi,\Phi(\rho))-I(\Psi\circ\Phi,\rho)\ge0.$$
--   The first term may be infinite. This identifies the natural domain for semicontinuity of preprocessing loss.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 7, Lemma 1: lower semicontinuity of the preprocessing mutual-information loss

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

/-- arXiv:2304.05388v3, Lemma 1, PDF p.7. The larger MI may be infinite. -/
theorem lemma_1 {A B C : Type} [Countable A] [Countable B] [Countable C]
    [Nonempty A] [Nonempty B] [Nonempty C] (Phi : Channel A B) (Psi : Channel B C) :
    (∀ rho : State A, mutualInformation rho.coefficients (Psi.val ∘ Phi.val) < ⊤ →
      mutualInformation rho.coefficients (Psi.val ∘ Phi.val) ≤
        mutualInformation (Phi.val rho.coefficients) Psi.val) ∧
    LowerSemicontinuousOn (fun rho : State A =>
      mutualInformation (Phi.val rho.coefficients) Psi.val -
        mutualInformation rho.coefficients (Psi.val ∘ Phi.val))
      {rho | mutualInformation rho.coefficients (Psi.val ∘ Phi.val) < ⊤} := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_lemma_4
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.lemma_4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:35:08.687385+00:00
-- url     : https://prove2.me/theorems/09f94204-006d-49ec-8d5c-be36f21262a3
-- title:
--   Lemma 4: simultaneous finite-ensemble approximation
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   For every Borel probability ensemble $\mu$ on trace-norm states there is one sequence of finite ensembles $\mu_n$, weakly converging to $\mu$, such that
--
--   $$\overline\rho(\mu_n)=\overline\rho(\mu)\quad(\forall n),\qquad \chi(\Phi(\mu_n))\longrightarrow\chi(\Phi(\mu))$$
--   for every output system and every channel $\Phi$ simultaneously. The sequence is chosen before the channel, and the limiting Holevo information may be infinite. This supplies simultaneous approximation with exact barycenter preservation.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 28, Lemma 4: simultaneous finite-ensemble approximation

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

/-- arXiv:2304.05388v3, Lemma 4, PDF p.28. A SINGLE sequence works for EVERY
output system/channel, and has the EXACT barycenter at each n. -/
theorem lemma_4 {A : Type} [Countable A] [Nonempty A] (mu : GeneralizedEnsemble A) :
    ∃ nu : ℕ → GeneralizedEnsemble A,
      (∀ n, HasFiniteSupport (nu n) ∧ averageCoefficients (nu n) = averageCoefficients mu) ∧
      Tendsto nu atTop (𝓝 mu) ∧
      ∀ (B : Type) [Countable B] [Nonempty B] (Phi : Channel A B),
        Tendsto (fun n => ensembleHolevo Phi.val (nu n)) atTop (𝓝 (ensembleHolevo Phi.val mu)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_proposition_15
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.proposition_15
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:49:48.669317+00:00
-- url     : https://prove2.me/theorems/9174d849-41fd-4757-9d90-e6fef0024468
-- title:
--   Proposition 15A–B: local continuity of output Holevo information
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   For strong channel convergence and weak convergence of Borel ensembles, output Holevo information is jointly lower semicontinuous everywhere, and the deficit $\Upsilon$ is jointly lower semicontinuous on finite output Holevo information. For $\Phi_n\to\Phi_0$ and $\mu_n\to\mu_0$,
--
--   $$I(\Phi_n,\overline\rho(\mu_n))\to I(\Phi_0,\overline\rho(\mu_0))<\infty\quad\Longrightarrow\quad\chi(\Phi_n(\mu_n))\to\chi(\Phi_0(\mu_0))<\infty.$$
--   The barycenters are computed from the laws, not separately postulated. This gives joint local continuity under finite MI convergence.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 44, Proposition 15A–B: local continuity of output Holevo information

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

/-- arXiv:2304.05388v3, Proposition 15A–B, PDF pp.43–44. Weak laws, strong
channels, and actual barycenters; no extra barycenter-convergence premise. -/
theorem proposition_15 {A B : Type} [Countable A] [Countable B] [Nonempty A] [Nonempty B] :
    LowerSemicontinuous (fun p : Channel A B × GeneralizedEnsemble A => ensembleHolevo p.1.val p.2) ∧
    LowerSemicontinuousOn (fun p : Channel A B × GeneralizedEnsemble A => ensembleInformationDeficit p.1.val p.2)
      {p | ensembleHolevo p.1.val p.2 < ⊤} ∧
    (∀ (mu : ℕ → GeneralizedEnsemble A) (mu0 : GeneralizedEnsemble A)
      (Phi : ℕ → Channel A B) (Phi0 : Channel A B),
      Tendsto mu atTop (𝓝 mu0) → Tendsto Phi atTop (𝓝 Phi0) →
      Tendsto (fun n => mutualInformation (averageCoefficients (mu n)) (Phi n).val) atTop
        (𝓝 (mutualInformation (averageCoefficients mu0) Phi0.val)) →
      mutualInformation (averageCoefficients mu0) Phi0.val < ⊤ →
      Tendsto (fun n => ensembleHolevo (Phi n).val (mu n)) atTop (𝓝 (ensembleHolevo Phi0.val mu0)) ∧
        ensembleHolevo Phi0.val mu0 < ⊤) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

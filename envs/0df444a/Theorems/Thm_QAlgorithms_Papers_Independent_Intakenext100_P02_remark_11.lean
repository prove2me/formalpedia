-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_remark_11
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.remark_11
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:50:44.351424+00:00
-- url     : https://prove2.me/theorems/2c418b77-25fb-40ff-a58f-5eeefea6e719
-- title:
--   Remark 11: entropy sufficient conditions for output Holevo convergence
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   Along strongly convergent channels and weakly convergent ensembles, suppose either $S(\overline\rho(\mu_n))\to S(\overline\rho(\mu_0))<\infty$ or $S(\Phi_n(\overline\rho(\mu_n)))\to S(\Phi_0(\overline\rho(\mu_0)))<\infty$. Then
--
--   $$\chi(\Phi_n(\mu_n))\longrightarrow\chi(\Phi_0(\mu_0))<\infty.$$
--   The hypotheses are alternatives, and the limiting entropy is finite in the selected alternative. This is the entropy sufficient condition for output Holevo convergence.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 44, Remark 11: entropy sufficient conditions for output Holevo convergence

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

/-- arXiv:2304.05388v3, Remark 11, PDF p.44. Either finite entropy limit suffices. -/
theorem remark_11 {A B : Type} [Countable A] [Countable B] [Nonempty A] [Nonempty B]
    (mu : ℕ → GeneralizedEnsemble A) (mu0 : GeneralizedEnsemble A)
    (Phi : ℕ → Channel A B) (Phi0 : Channel A B)
    (hmu : Tendsto mu atTop (𝓝 mu0)) (hPhi : Tendsto Phi atTop (𝓝 Phi0))
    (hentropy :
      (Tendsto (fun n => extendedEntropyNats (averageCoefficients (mu n))) atTop
        (𝓝 (extendedEntropyNats (averageCoefficients mu0))) ∧ extendedEntropyNats (averageCoefficients mu0) < ⊤) ∨
      (Tendsto (fun n => extendedEntropyNats ((Phi n).val (averageCoefficients (mu n)))) atTop
        (𝓝 (extendedEntropyNats (Phi0.val (averageCoefficients mu0)))) ∧
          extendedEntropyNats (Phi0.val (averageCoefficients mu0)) < ⊤)) :
    Tendsto (fun n => ensembleHolevo (Phi n).val (mu n)) atTop (𝓝 (ensembleHolevo Phi0.val mu0)) ∧
      ensembleHolevo Phi0.val mu0 < ⊤ := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

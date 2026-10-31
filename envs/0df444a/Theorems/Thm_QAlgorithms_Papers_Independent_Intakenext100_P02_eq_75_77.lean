-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_eq_75_77
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.eq_75_77
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:34:26.315609+00:00
-- url     : https://prove2.me/theorems/7e50226e-f611-4256-8160-ec169cdc7083
-- title:
--   Ensemble forms of the generalized correlation relations (75)–(77)
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   Let $\mu=\{p_i,\rho_i\}$ have actual average $\rho$, let $\widehat\rho$ be its given purification and choose a discrete $M_\mu$ on $R$ satisfying $p_i\rho_i=\operatorname{Tr}_R[(I\otimes M_i)\widehat\rho]$. Construct $\omega$ from the given dilation as above. Then
--
--   $$C_R^{M_\mu}((\Phi\otimes\mathrm{Id})(\widehat\rho))=C_R^{M_\mu}(\omega_{BR})=\chi(\Phi(\mu)),$$
--   $$\mathrm{ER}((\Phi\otimes\mathrm{Id})(\widehat\rho),I_B\otimes M_\mu)=\mathrm{ER}(\omega_{BR},I_B\otimes M_\mu)=C_R^{M_\mu}(\omega_{ER})=\chi(\widehat\Phi(\mu)).$$
--   If $\chi(\Phi(\mu))<\infty$, both corresponding unoptimized discords equal $I(\Phi,\rho)-\chi(\Phi(\mu))$. If every signal is pure, an inducing rank-one POVM exists. The displayed Holevo quantities are the relative-entropy sums of the given ensemble.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 27, Ensemble forms of the generalized correlation relations (75)–(77)

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

/-- arXiv:2304.05388v3, ensemble relations (75)–(77), PDF p.27. No assumed
independent success law or unconstrained replacement ensemble is introduced. -/
theorem eq_75_77 {A B E R : Type} [Countable A] [Countable B] [Countable E] [Countable R]
    [Nonempty A] [Nonempty B] [Nonempty E] [Nonempty R]
    (Phi : Channel A B) (PhiC : Channel A E)
    (V : Hilbert A →ₗᵢ[ℂ] Hilbert (B × E))
    (hV : ∀ rho : State A,
      Phi.val rho.coefficients = traceSecond (conjugateCoeff V.toContinuousLinearMap rho.coefficients) ∧
      PhiC.val rho.coefficients = traceFirst (conjugateCoeff V.toContinuousLinearMap rho.coefficients))
    (e : CountableStateEnsemble A) (psi : PureState (A × R))
    (haverage : traceSecond psi.val.coefficients = countableAverageCoefficients e)
    (M : DiscretePOVM R ℕ) (hM : Induces M psi e) :
    let omega := purifiedDilationCoefficients V psi
    classicalM M (tensorApply Phi.val psi.val.coefficients) = classicalM M (tripartiteAC omega) ∧
    classicalM M (tripartiteAC omega) = countableOutputHolevo Phi.val e ∧
    (countableOutputHolevo Phi.val e < ⊤ →
      discordM M (tensorApply Phi.val psi.val.coefficients) = discordM M (tripartiteAC omega) ∧
      discordM M (tripartiteAC omega) = mutualInformation (countableAverageCoefficients e) Phi.val - countableOutputHolevo Phi.val e) ∧
    localER M (tensorApply Phi.val psi.val.coefficients) = localER M (tripartiteAC omega) ∧
    localER M (tripartiteAC omega) = classicalM M (traceA omega) ∧
    classicalM M (traceA omega) = countableOutputHolevo PhiC.val e ∧
    ((∀ i, e.state i ∈ pureStates A) →
      ∃ N : DiscretePOVM R ℕ, Induces N psi e ∧ HasRankOneEffects N) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_eq_111
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.eq_111
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:46:19.534446+00:00
-- url     : https://prove2.me/theorems/bebb2f27-82a7-4ec7-bf29-cc2d5649caaf
-- title:
--   Entropic disturbance bounded by unoptimized complementary discord (111)
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   For every generalized ensemble with $\chi(\mu)<\infty$,
--
--   $$\chi(\mu)-\chi(\Phi(\mu))\le I(\widehat\Phi,\overline\rho(\mu))-\chi(\widehat\Phi(\mu)).$$
--   For a discrete ensemble and an inducing reference POVM $M_\mu$ computed by the mixed-state Born rule from a given purification, the right side equals $D_R^{M_\mu}((\widehat\Phi\otimes\mathrm{Id})(\widehat\rho))$. If all discrete signals are pure, the inequality is an equality and a rank-one inducing POVM exists. Only the first inequality is asserted for continuous ensembles; no arbitrary-outcome conditional density disintegration is presumed.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 41, Entropic disturbance bounded by unoptimized complementary discord (111)

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

/-- arXiv:2304.05388v3, (111), PDF p.41. The first inequality extends to
continuous ensembles; a reference POVM is asserted ONLY for the discrete case. -/
theorem eq_111 {A B E : Type} [Countable A] [Countable B] [Countable E]
    [Nonempty A] [Nonempty B] [Nonempty E] (Phi : Channel A B) (PhiC : Channel A E)
    (hcomp : Complementary Phi PhiC) :
    (∀ mu : GeneralizedEnsemble A, ensembleHolevo id mu < ⊤ →
      ensembleHolevo id mu - ensembleHolevo Phi.val mu ≤ ensembleInformationDeficit PhiC.val mu) ∧
    (∀ (R : Type) [Countable R] [Nonempty R] (e : CountableStateEnsemble A)
      (psi : PureState (A × R)) (M : DiscretePOVM R ℕ),
      traceSecond psi.val.coefficients = countableAverageCoefficients e → Induces M psi e →
      countableOutputHolevo id e < ⊤ →
      countableOutputHolevo id e - countableOutputHolevo Phi.val e ≤
        mutualInformation (countableAverageCoefficients e) PhiC.val - countableOutputHolevo PhiC.val e ∧
      mutualInformation (countableAverageCoefficients e) PhiC.val - countableOutputHolevo PhiC.val e =
        discordM M (tensorApply PhiC.val psi.val.coefficients) ∧
      ((∀ i, e.state i ∈ pureStates A) →
        countableOutputHolevo id e - countableOutputHolevo Phi.val e =
          mutualInformation (countableAverageCoefficients e) PhiC.val - countableOutputHolevo PhiC.val e ∧
        ∃ N : DiscretePOVM R ℕ, Induces N psi e ∧ HasRankOneEffects N)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

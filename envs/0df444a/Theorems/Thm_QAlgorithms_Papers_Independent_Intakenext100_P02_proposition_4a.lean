-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_proposition_4a
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.proposition_4a
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:26:50.182121+00:00
-- url     : https://prove2.me/theorems/4a1cebad-5177-40a8-be58-eab7a6c87b58
-- title:
--   Proposition 4A)
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   Write $\widehat D_B^M$ for the all-state unoptimized extension. It is nonnegative, lower semicontinuous and monotone under channels on $A$, agrees with $D_B^M$ on $C_B^M<\infty$, and is the unique extension with these properties. For every state,
--
--   $$\widehat D_B^M(\omega)=\sup_{\Phi\in\mathcal F_A}D_B^M((\Phi\otimes\mathrm{Id})(\omega))=\lim_nD_B^M((\Phi_n\otimes\mathrm{Id})(\omega)).$$
--   Here $\mathcal F_A$ consists of channels with finite-dimensional output support, and the last equality holds for every sequence in $\mathcal F_A$ converging strongly to the identity. The local definition uses the equivalent supremum formula; all regularity and uniqueness clauses remain theorem conclusions.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 21, Proposition 4A)

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

/-- arXiv:2304.05388v3, Proposition 4A, PDF pp.21–23. Includes agreement,
l.s.c., channel monotonicity, uniqueness, supremum and EVERY approximation limit. -/
theorem proposition_4a {A B K : Type} [Countable A] [Countable B]
    [Nonempty A] [Nonempty B] [Countable K] (M : DiscretePOVM B K) :
    LowerSemicontinuous (fun omega : State (A × B) => extendedDiscordM M omega.coefficients) ∧
    LocalMonotone (extendedDiscordM (A := A) (B := B) M) ∧
    (∀ omega : State (A × B), classicalM M omega.coefficients < ⊤ →
      extendedDiscordM M omega.coefficients = discordM M omega.coefficients) ∧
    (∀ f : Matrix (A × B) (A × B) ℂ → ℝ≥0∞,
      LowerSemicontinuous (fun omega : State (A × B) => f omega.coefficients) →
      LocalMonotone f →
      (∀ omega : State (A × B), classicalM M omega.coefficients < ⊤ →
        f omega.coefficients = discordM M omega.coefficients) →
      ∀ omega : State (A × B), f omega.coefficients = extendedDiscordM M omega.coefficients) ∧
    (∀ omega : State (A × B), extendedDiscordM M omega.coefficients =
      ⨆ Phi : {Phi : Channel A A // FiniteOutput Phi}, discordM M (tensorApply Phi.val.val omega.coefficients)) ∧
    (∀ (Phi : ℕ → Channel A A), (∀ n, FiniteOutput (Phi n)) →
      StronglyConverges (fun n => (Phi n).val) id →
      ∀ omega : State (A × B), Tendsto (fun n => discordM M (tensorApply (Phi n).val omega.coefficients))
        atTop (𝓝 (extendedDiscordM M omega.coefficients))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

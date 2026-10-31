-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_proposition_4c_operation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.proposition_4c_operation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:29:47.446391+00:00
-- url     : https://prove2.me/theorems/919ec23b-4a71-470e-9825-784957f0c5c4
-- title:
--   Proposition 4C: valid operation inequality and A-unitary invariance
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   For every state, discrete $M$, and quantum operation $\Phi$ on $A$ with $c=\operatorname{Tr}\Phi(\omega_A)>0$,
--
--   $$c\widehat D_B^M((\Phi\otimes\mathrm{Id})(\omega)/c)\le\widehat D_B^M(\omega).$$
--   In addition, $\widehat D_B^M$ is invariant under every unitary on $A$. The printed fixed-$M$ invariance under arbitrary unitaries on $B$ is false and is exclusively deferred. This retains the valid operation and unmeasured-unitary claims.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 21, Proposition 4C: valid operation inequality and A-unitary invariance

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

/-- arXiv:2304.05388v3, valid part of Proposition 4C, PDF p.21.
Printed fixed-M B-unitary invariance is false and is deferred separately.
Retained: the operation inequality and invariance under unitaries on A. -/
theorem proposition_4c_operation {A B K : Type} [Countable A] [Countable B]
    [Nonempty A] [Nonempty B] [Countable K] (M : DiscretePOVM B K) :
    (∀ (omega : State (A × B)) (Phi : Matrix A A ℂ → Matrix A A ℂ),
      IsQuantumOperation Phi → 0 < operatorTrace (Phi (traceSecond omega.coefficients)) →
      ENNReal.ofReal (operatorTrace (Phi (traceSecond omega.coefficients))) *
        extendedDiscordM M (((operatorTrace (Phi (traceSecond omega.coefficients)))⁻¹ : ℂ) •
          tensorApply Phi omega.coefficients) ≤ extendedDiscordM M omega.coefficients) ∧
    (∀ (omega : State (A × B)) (U : Hilbert A ≃ₗᵢ[ℂ] Hilbert A),
      extendedDiscordM M (tensorApply (conjugateCoeff U.toLinearIsometry.toContinuousLinearMap) omega.coefficients) =
        extendedDiscordM M omega.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

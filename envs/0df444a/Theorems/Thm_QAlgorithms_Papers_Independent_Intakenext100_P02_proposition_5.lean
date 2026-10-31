-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_proposition_5
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.proposition_5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:32:11.421913+00:00
-- url     : https://prove2.me/theorems/98e3f04d-5867-4ed1-9be9-73b6dbf8f610
-- title:
--   Proposition 5A–E: the two optimized discord extensions
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   The supremum extension $\widetilde D_B$ is the unique nonnegative lower semicontinuous extension of $D_B$ that is monotone under channels on $A$. For every finite-output channel sequence strongly approaching the identity,
--
--   $$\widetilde D_B(\omega)=\lim_n D_B((\Phi_n\otimes\mathrm{Id})(\omega)).$$
--   Both $\widetilde D_B$ and $\widehat D_B$ vanish on all q-c states. If the general zero-discord characterization on $C_B<\infty$ is true, each zero set is exactly the q-c set. Both extensions are invariant under local unitaries, satisfy $cf((\Phi\otimes\mathrm{Id})(\omega)/c)\le f(\omega)$ for every operation with actual success probability $c>0$, and satisfy $pf(\rho)+(1-p)f(\sigma)\le f(p\rho+(1-p)\sigma)+h_2(p)$. If $S(\omega)<\infty$, both obey $S(\omega_B)\le f(\omega)+S(\omega)$ and are infinite when $C_B(\omega)=\infty$. Only the supremum extension receives the uniqueness and semicontinuity conclusions.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 24, Proposition 5A–E: the two optimized discord extensions

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

/-- arXiv:2304.05388v3, Proposition 5A–E, PDF pp.24–25. Uniqueness and l.s.c.
are asserted only for the supremum extension. The converse zero-set claim is
CONDITIONAL on the general zero-discord conjecture on its natural domain. -/
theorem proposition_5 {A B : Type} [Countable A] [Countable B] [Nonempty A] [Nonempty B] :
    LowerSemicontinuous (fun omega : State (A × B) => supDiscord omega.coefficients) ∧
    LocalMonotone (supDiscord (A := A) (B := B)) ∧
    (∀ omega : State (A × B), discreteClassicalCorrelation omega.coefficients < ⊤ →
      supDiscord omega.coefficients = discreteOptimizedDiscord omega.coefficients) ∧
    (∀ f : Matrix (A × B) (A × B) ℂ → ℝ≥0∞,
      LowerSemicontinuous (fun omega : State (A × B) => f omega.coefficients) →
      LocalMonotone f →
      (∀ omega : State (A × B), discreteClassicalCorrelation omega.coefficients < ⊤ →
        f omega.coefficients = discreteOptimizedDiscord omega.coefficients) →
      ∀ omega : State (A × B), f omega.coefficients = supDiscord omega.coefficients) ∧
    (∀ (Phi : ℕ → Channel A A), (∀ n, FiniteOutput (Phi n)) →
      StronglyConverges (fun n => (Phi n).val) id →
      ∀ omega : State (A × B), Tendsto (fun n => discreteOptimizedDiscord (tensorApply (Phi n).val omega.coefficients))
        atTop (𝓝 (supDiscord omega.coefficients))) ∧
    (∀ omega : State (A × B), IsQC omega.coefficients →
      infDiscord omega.coefficients = 0 ∧ supDiscord omega.coefficients = 0) ∧
    ((∀ omega : State (A × B), discreteClassicalCorrelation omega.coefficients < ⊤ →
        discreteOptimizedDiscord omega.coefficients = 0 → IsQC omega.coefficients) →
      ∀ omega : State (A × B),
        (infDiscord omega.coefficients = 0 ↔ IsQC omega.coefficients) ∧
        (supDiscord omega.coefficients = 0 ↔ IsQC omega.coefficients)) ∧
    (∀ f ∈ ({infDiscord, supDiscord} : Set (Matrix (A × B) (A × B) ℂ → ℝ≥0∞)),
      (∀ (omega : State (A × B)) (U : Hilbert A ≃ₗᵢ[ℂ] Hilbert A)
        (V : Hilbert B ≃ₗᵢ[ℂ] Hilbert B),
        f (channelTensorAction (conjugateCoeff U.toLinearIsometry.toContinuousLinearMap)
          (conjugateCoeff V.toLinearIsometry.toContinuousLinearMap) omega.coefficients) = f omega.coefficients) ∧
      (∀ (omega : State (A × B)) (Phi : Matrix A A ℂ → Matrix A A ℂ),
        IsQuantumOperation Phi → 0 < operatorTrace (Phi (traceSecond omega.coefficients)) →
        ENNReal.ofReal (operatorTrace (Phi (traceSecond omega.coefficients))) *
          f (((operatorTrace (Phi (traceSecond omega.coefficients)))⁻¹ : ℂ) •
            tensorApply Phi omega.coefficients) ≤ f omega.coefficients) ∧
      (∀ (rho sigma : State (A × B)) (p : ℝ), 0 ≤ p → p ≤ 1 →
        ENNReal.ofReal p * f rho.coefficients + ENNReal.ofReal (1-p) * f sigma.coefficients ≤
          f (convexOperatorMixture p rho.coefficients sigma.coefficients) + binaryEntropy p) ∧
      (∀ omega : State (A × B), extendedEntropyNats omega.coefficients < ⊤ →
        extendedEntropyNats (traceFirst omega.coefficients) ≤ f omega.coefficients +
          extendedEntropyNats omega.coefficients) ∧
      (∀ omega : State (A × B), extendedEntropyNats omega.coefficients < ⊤ →
        discreteClassicalCorrelation omega.coefficients = ⊤ → f omega.coefficients = ⊤)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

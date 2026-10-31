-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_proposition_1
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.proposition_1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:10:20.641315+00:00
-- url     : https://prove2.me/theorems/5319bfd8-58f3-407d-9a5e-2e1d3c940f33
-- title:
--   Proposition 1A–C: local entropy reduction
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   For every fixed discrete POVM $M$ on $B$, $R_M$ is nonnegative, concave and lower semicontinuous. For normalized $\omega,\rho,\sigma$ and $p\in[0,1]$,
--
--   $$R_M(\omega)\le\min\{S(\omega),S(\omega_B)\},\qquad R_M(p\rho+(1-p)\sigma)\le pR_M(\rho)+(1-p)R_M(\sigma)+h_2(p).$$
--   The increment $R_M((\Phi\otimes\mathrm{Id}_B)(\omega))-R_M(\omega)$ is nonnegative and lower semicontinuous on $R_M<\infty$ for every channel on the unmeasured system, whose output may be another separable system. If $\omega_n\to\omega_0$ and either $S(\omega_n)\to S(\omega_0)<\infty$ or $S((\omega_n)_B)\to S((\omega_0)_B)<\infty$, then $R_M(\omega_n)\to R_M(\omega_0)<\infty$. These are the basic regularity and continuity properties of local entropy reduction.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 9, Proposition 1A–C: local entropy reduction

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

/-- arXiv:2304.05388v3, Proposition 1A–C, PDF pp.9–10. -/
theorem proposition_1 {A B : Type} [Countable A] [Countable B]
    [Nonempty A] [Nonempty B] {K : Type} [Countable K] (M : DiscretePOVM B K) :
    (∀ omega : State (A × B), 0 ≤ localER M omega.coefficients ∧
      localER M omega.coefficients ≤ min (extendedEntropyNats omega.coefficients)
        (extendedEntropyNats (traceFirst omega.coefficients))) ∧
    LowerSemicontinuous (fun omega : State (A × B) => localER M omega.coefficients) ∧
    (∀ (rho sigma : State (A × B)) (p : ℝ), 0 ≤ p → p ≤ 1 →
      ENNReal.ofReal p * localER M rho.coefficients +
        ENNReal.ofReal (1-p) * localER M sigma.coefficients ≤
          localER M (convexOperatorMixture p rho.coefficients sigma.coefficients) ∧
      localER M (convexOperatorMixture p rho.coefficients sigma.coefficients) ≤
        ENNReal.ofReal p * localER M rho.coefficients +
          ENNReal.ofReal (1-p) * localER M sigma.coefficients + binaryEntropy p) ∧
    (∀ (D : Type) [Countable D] [Nonempty D] (Phi : Channel A D),
      (∀ omega : State (A × B), localER M omega.coefficients < ⊤ →
        localER M omega.coefficients ≤ localER M (tensorApply Phi.val omega.coefficients)) ∧
      LowerSemicontinuousOn (fun omega : State (A × B) =>
        localER M (tensorApply Phi.val omega.coefficients) - localER M omega.coefficients)
        {omega | localER M omega.coefficients < ⊤}) ∧
    (∀ (omega : ℕ → State (A × B)) (omega0 : State (A × B)),
      Tendsto omega atTop (𝓝 omega0) →
      ((Tendsto (fun n => extendedEntropyNats (omega n).coefficients) atTop
          (𝓝 (extendedEntropyNats omega0.coefficients)) ∧ extendedEntropyNats omega0.coefficients < ⊤) ∨
       (Tendsto (fun n => extendedEntropyNats (traceFirst (omega n).coefficients)) atTop
          (𝓝 (extendedEntropyNats (traceFirst omega0.coefficients))) ∧
            extendedEntropyNats (traceFirst omega0.coefficients) < ⊤)) →
      Tendsto (fun n => localER M (omega n).coefficients) atTop (𝓝 (localER M omega0.coefficients)) ∧
        localER M omega0.coefficients < ⊤) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

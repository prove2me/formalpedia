-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_corollary_3
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.corollary_3
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:15:39.327256+00:00
-- url     : https://prove2.me/theorems/bd7f84fc-f49c-4518-986c-039ade38a3b9
-- title:
--   Corollary 3: energy-constrained entropy-reduction continuity
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   Let $X$ be either $B$ or $AB$ and let $H\ge0$ on $H_X$ satisfy $\lim_{\beta\downarrow0}(\operatorname{Tr}e^{-\beta H})^\beta=1$. Put $F_H(E)=\sup_{\operatorname{Tr}H\tau\le E}S(\tau)$. For $\operatorname{Tr}H\rho_X,\operatorname{Tr}H\sigma_X\le E$, $E\ge0$, and $0\le\delta\le1$, assume either $F(\rho,\sigma)\ge1-\delta^2$ or $(2-\varepsilon)\varepsilon\le\delta^2$, where $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1^2$ and $\varepsilon=\frac12\|\rho-\sigma\|_1$. Then both entropy reductions are finite and
--
--   $$|R_M(\rho)-R_M(\sigma)|\le\delta F_H(2E/\delta^2)+g(\delta).$$
--   At $\delta=0$ the right side is defined to be zero. For fixed admissible $H,E$ the bound tends to zero as $\delta\downarrow0$. This provides uniform continuity on the constrained input-state set.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 11, Corollary 3: energy-constrained entropy-reduction continuity

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

open QAlgorithms.Papers.Independent.Claimed50.P13 (PositiveObservable closedFormExpectation)

open QAlgorithms.Papers.Independent.Frontier18.P18 (stateSquareRoot)

/-- arXiv:2304.05388v3, Corollary 3 and following continuity conclusion, PDF p.11.
Both distance alternatives, either subsystem, and the zero-radius convention.
The output of a channel is subject to NO energy premise. -/
theorem corollary_3 {A B K : Type} [Countable A] [Countable B]
    [Nonempty A] [Nonempty B] [Countable K] (M : DiscretePOVM B K)
    (constraint : EnergyConstraint A B) (hregular : constraint.regular) :
    (∀ (rho sigma : State (A × B)) (E radius : ℝ), 0 ≤ E → 0 ≤ radius → radius ≤ 1 →
      constraint.mean rho.coefficients ≤ ENNReal.ofReal E →
      constraint.mean sigma.coefficients ≤ ENNReal.ofReal E →
      (ENNReal.ofReal (1-radius^2) ≤ traceClassSquaredFidelity rho sigma ∨
        (2-(traceSize (rho.coefficients-sigma.coefficients)).toReal/2) *
          ((traceSize (rho.coefficients-sigma.coefficients)).toReal/2) ≤ radius^2) →
      localER M rho.coefficients < ⊤ ∧ localER M sigma.coefficients < ⊤ ∧
      ENNReal.ofReal |(localER M rho.coefficients).toReal - (localER M sigma.coefficients).toReal| ≤
        constraint.bound E radius) ∧
    (∀ E : ℝ, 0 ≤ E → (∃ rho : State (A × B), constraint.mean rho.coefficients ≤ ENNReal.ofReal E) →
      Tendsto (fun radius : ℝ => constraint.bound E radius) (𝓝[>] 0) (𝓝 0)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

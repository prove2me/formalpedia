-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_fixed_average_continuity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.fixed_average_continuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:51:25.773278+00:00
-- url     : https://prove2.me/theorems/3208003a-e495-4ccf-97ea-2f3361f7837e
-- title:
--   Unnumbered pp.44–45: fixed-average continuity beyond finite entropies
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   Fix $\Phi,\rho$ with $I(\Phi,\rho)<\infty$. For every weakly convergent sequence of generalized ensembles with exact average $\rho$ at every term and at the limit,
--
--   $$\chi(\Phi(\mu_n))\longrightarrow\chi(\Phi(\mu_0))<\infty.$$
--   There exist bipartite states $\omega_{BC}$ with both marginal entropies infinite and finite QMI. For every such $\omega$, purify it on $BC\otimes\ell^2(\mathbb N)$, take the actual $B\ell^2$ marginal as input, and trace out the auxiliary factor. This produces infinite input and output entropy but finite channel MI. Thus the continuity statement applies beyond both finite-entropy alternatives.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 44, Unnumbered pp.44–45: fixed-average continuity beyond finite entropies

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

/-- arXiv:2304.05388v3, unnumbered pp.44–45 and footnote 3. Exact-average
continuity and the explicit purification/partial-trace construction beyond
finite marginal entropies are both retained. -/
theorem fixed_average_continuity :
    (∀ (A B : Type) [Countable A] [Countable B] [Nonempty A] [Nonempty B]
      (Phi : Channel A B) (rho : State A), mutualInformation rho.coefficients Phi.val < ⊤ →
      ∀ (mu : ℕ → GeneralizedEnsemble A) (mu0 : GeneralizedEnsemble A),
        Tendsto mu atTop (𝓝 mu0) →
        (∀ n, averageCoefficients (mu n) = rho.coefficients) →
        averageCoefficients mu0 = rho.coefficients →
        Tendsto (fun n => ensembleHolevo Phi.val (mu n)) atTop (𝓝 (ensembleHolevo Phi.val mu0)) ∧
          ensembleHolevo Phi.val mu0 < ⊤) ∧
    (∃ omega : State (ℕ × ℕ), extendedEntropyNats (traceFirst omega.coefficients) = ⊤ ∧
      extendedEntropyNats (traceSecond omega.coefficients) = ⊤ ∧ qmi omega.coefficients < ⊤) ∧
    (∀ (B C : Type) [Countable B] [Countable C] [Nonempty B] [Nonempty C]
      (omega : State (B × C)),
      extendedEntropyNats (traceFirst omega.coefficients) = ⊤ →
      extendedEntropyNats (traceSecond omega.coefficients) = ⊤ → qmi omega.coefficients < ⊤ →
      ∃ psi : PureState ((B × C) × ℕ), traceSecond psi.val.coefficients = omega.coefficients ∧
        extendedEntropyNats (tripartiteAC psi.val.coefficients) = ⊤ ∧
        extendedEntropyNats (traceSecond (tripartiteAC psi.val.coefficients)) = ⊤ ∧
        mutualInformation (tripartiteAC psi.val.coefficients) traceSecond < ⊤) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

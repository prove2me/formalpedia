-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_corollary_7
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.corollary_7
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:36:32.475374+00:00
-- url     : https://prove2.me/theorems/02bfa1a8-e485-471b-b8fe-7c820ecac5c0
-- title:
--   Corollary 7: privacy continuity and exact witnesses
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   Define signed ensemble privacy by $\pi(\Phi,\mu)=\chi(\Phi(\mu))-\chi(\widehat\Phi(\mu))$. If $d=\dim H_A<\infty$, or $d=\operatorname{rank}\overline\rho(\mu)<\infty$, and $\frac12\|\Phi-\Psi\|_\diamond\le\varepsilon$ with $\varepsilon\ge0$, all Holevo terms are finite and
--
--   $$|\pi(\Phi,\mu)-\pi(\Psi,\mu)|\le2\varepsilon\ln d+2g(\varepsilon).$$
--   For every $d\ge2$, $\varepsilon\in[0,1]$, erasure probabilities $0,\varepsilon$ and a pure ensemble of chaotic average give exact distance $\varepsilon$ and privacy difference $2\varepsilon\ln d$. The ratio to the full bound tends to one at fixed positive $\varepsilon$ as $d\to\infty$. Privacy may be negative.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 30, Corollary 7: privacy continuity and exact witnesses

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

/-- arXiv:2304.05388v3, Corollary 7, PDF p.30. Privacy is signed, unlike the
optimized private capacity. Both finite-input and finite-average-rank regimes. -/
theorem corollary_7 :
    (∀ (A B E F : Type) [Countable A] [Countable B] [Countable E] [Countable F]
      [Nonempty A] [Nonempty B] [Nonempty E] [Nonempty F]
      (Phi Psi : Channel A B) (PhiC : Channel A E) (PsiC : Channel A F),
      Complementary Phi PhiC → Complementary Psi PsiC →
      ∀ (mu : GeneralizedEnsemble A) (eps : ℝ) (d : ℕ), 0 ≤ eps →
        (dimensionCount A = (d : ℕ∞) ∨
          QAlgorithms.Papers.Independent.Gap48.P45.operatorRank (boundedOperator (averageCoefficients mu)) = (d : ℕ∞)) →
        halfTraceClassDiamondDistance Phi.val Psi.val ≤ ENNReal.ofReal eps →
        ensembleHolevo Phi.val mu < ⊤ ∧ ensembleHolevo Psi.val mu < ⊤ ∧
        ensembleHolevo PhiC.val mu < ⊤ ∧ ensembleHolevo PsiC.val mu < ⊤ ∧
        |privacy Phi.val PhiC.val mu - privacy Psi.val PsiC.val mu| ≤ 2 * eps * Real.log d + 2 * correctionG eps) ∧
    (∀ (d : ℕ) (eps : ℝ), 2 ≤ d → 0 ≤ eps → eps ≤ 1 →
      ∃ (Phi Psi PhiC PsiC : Channel (Fin d) (Option (Fin d))) (mu : GeneralizedEnsemble (Fin d)),
        IsErasureWitness Phi Psi PhiC PsiC eps ∧ averageCoefficients mu = uniformDensityCoefficients (Fin d) ∧
        (mu : Measure (State (Fin d))).support ⊆ pureStates (Fin d) ∧
        halfTraceClassDiamondDistance Phi.val Psi.val = ENNReal.ofReal eps ∧
        |privacy Phi.val PhiC.val mu - privacy Psi.val PsiC.val mu| = 2 * eps * Real.log d) ∧
    (∀ eps : ℝ, 0 < eps → eps ≤ 1 → Tendsto
      (fun d : ℕ => (2 * eps * Real.log d) / (2 * eps * Real.log d + 2 * correctionG eps)) atTop (𝓝 1)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_proposition_6
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.proposition_6
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:35:49.128138+00:00
-- url     : https://prove2.me/theorems/34a312e0-3278-4d57-8a31-3d4fff87e3d4
-- title:
--   Proposition 6: finite-input-dimension output and complementary Holevo bounds
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   Let $\Phi,\Psi:A\to B$ be channels and let $\mu$ be any generalized ensemble. Suppose $d=\dim H_A<\infty$, or more generally $d=\operatorname{rank}\overline\rho(\mu)<\infty$. If $\varepsilon\ge0$ and $\frac12\|\Phi-\Psi\|_\diamond\le\varepsilon$, then all four Holevo quantities are finite and
--
--   $$|\chi(\Phi(\mu))-\chi(\Psi(\mu))|,\ |\chi(\widehat\Phi(\mu))-\chi(\widehat\Psi(\mu))|\le\varepsilon\ln d+g(\varepsilon).$$
--   Complementary outputs may use different environments. For every $d\ge2$ and $\varepsilon\in[0,1]$, the erasure channels at probabilities $0,\varepsilon$, their complements, and a pure ensemble of chaotic average give exact diamond distance $\varepsilon$ and both differences $\varepsilon\ln d$. For fixed positive $\varepsilon$, the ratio of this witness value to the full bound tends to one as $d\to\infty$.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 28, Proposition 6: finite-input-dimension output and complementary Holevo bounds

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

/-- arXiv:2304.05388v3, Proposition 6, PDF pp.28–30. Both bounds, the finite
barycenter-rank refinement, exact simultaneous erasure witnesses, and the
fixed-positive-epsilon ratio expressing their large-d sharpness. -/
theorem proposition_6 :
    (∀ (A B E F : Type) [Countable A] [Countable B] [Countable E] [Countable F]
      [Nonempty A] [Nonempty B] [Nonempty E] [Nonempty F]
      (Phi Psi : Channel A B) (PhiC : Channel A E) (PsiC : Channel A F),
      Complementary Phi PhiC → Complementary Psi PsiC →
      ∀ (mu : GeneralizedEnsemble A) (eps : ℝ) (d : ℕ), 0 ≤ eps →
        (dimensionCount A = (d : ℕ∞) ∨
          QAlgorithms.Papers.Independent.Gap48.P45.operatorRank (boundedOperator (averageCoefficients mu)) = (d : ℕ∞)) →
        halfTraceClassDiamondDistance Phi.val Psi.val ≤ ENNReal.ofReal eps →
        HolevoComparison Phi.val Psi.val mu (eps * Real.log d + correctionG eps) ∧
        HolevoComparison PhiC.val PsiC.val mu (eps * Real.log d + correctionG eps)) ∧
    (∀ (d : ℕ) (eps : ℝ), 2 ≤ d → 0 ≤ eps → eps ≤ 1 →
      ∃ (Phi Psi PhiC PsiC : Channel (Fin d) (Option (Fin d))) (mu : GeneralizedEnsemble (Fin d)),
        IsErasureWitness Phi Psi PhiC PsiC eps ∧
        averageCoefficients mu = uniformDensityCoefficients (Fin d) ∧ (mu : Measure (State (Fin d))).support ⊆ pureStates (Fin d) ∧
        halfTraceClassDiamondDistance Phi.val Psi.val = ENNReal.ofReal eps ∧
        |(ensembleHolevo Phi.val mu).toReal - (ensembleHolevo Psi.val mu).toReal| = eps * Real.log d ∧
        |(ensembleHolevo PhiC.val mu).toReal - (ensembleHolevo PsiC.val mu).toReal| = eps * Real.log d) ∧
    (∀ eps : ℝ, 0 < eps → eps ≤ 1 → Tendsto
      (fun d : ℕ => (eps * Real.log d) / (eps * Real.log d + correctionG eps)) atTop (𝓝 1)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_example_3
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.example_3
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:48:29.107505+00:00
-- url     : https://prove2.me/theorems/73ca3a67-2b5d-41ad-a910-e291996257a0
-- title:
--   Example 3: erasure q-c proximity and Holevo-capacity lower bound
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   For finite input dimension $d\ge1$, $p\in[0,1]$, and erasure $\Omega_p$ with complement $\Omega_{1-p}$,
--
--   $$\varepsilon_{\widehat\Omega_p}\le p(1-d^{-2}),\qquad\overline C(\Omega_p)=(1-p)\ln d,$$
--   $$\overline C(\Omega_p)\ge(1-p+p/d^2)\ln d-g(p(1-d^{-2})).$$
--   For $p>0$ and $d\ge2$, the expression $(1-\varepsilon_{\widehat\Omega_p})\ln d$ strictly exceeds the actual capacity. Thus the negative correction term cannot be deleted. The raw erasure maps are linked to a genuine complementary channel pair.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 42, Example 3: erasure q-c proximity and Holevo-capacity lower bound

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

/-- arXiv:2304.05388v3, Example 3, PDF p.42. Exact erasure capacity, explicit
proximity upper bound, the resulting lower bound, and necessity of -g. -/
theorem example_3 {A : Type} [Fintype A] [Nonempty A] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∃ Phi PhiC : Channel A (Option A), Complementary Phi PhiC ∧
      ∀ X, IsTraceClass X → Phi.val X = flaggedTraceClassErasure p X ∧ PhiC.val X = flaggedTraceClassErasure (1-p) X) ∧
    qcProximity (flaggedTraceClassErasure (1-p) (A := A)) ≤ p * (1 - 1 / (Fintype.card A : ℝ)^2) ∧
    generalizedHolevoCapacity (flaggedTraceClassErasure p (A := A)) = ENNReal.ofReal ((1-p) * Real.log (Fintype.card A)) ∧
    (1-p + p/(Fintype.card A : ℝ)^2) * Real.log (Fintype.card A) -
      correctionG (p * (1 - 1/(Fintype.card A : ℝ)^2)) ≤
        (generalizedHolevoCapacity (flaggedTraceClassErasure p (A := A))).toReal ∧
    (0 < p → 2 ≤ Fintype.card A → (generalizedHolevoCapacity (flaggedTraceClassErasure p (A := A))).toReal <
      (1 - qcProximity (flaggedTraceClassErasure (1-p) (A := A))) * Real.log (Fintype.card A)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

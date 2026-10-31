-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_proposition_10
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.proposition_10
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:40:30.983373+00:00
-- url     : https://prove2.me/theorems/82642cc8-d167-40ec-8b2f-7955a26db44e
-- title:
--   Proposition 10: finite-input private-capacity continuity bounds
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   For channels with finite input dimension $d\ge1$, define unregularized private capacity by the supremum of signed ensemble privacy over all generalized ensembles. For $\varepsilon\ge0$, closeness of either the channels or some pair of their complements in a common environment by half diamond norm at most $\varepsilon$ implies
--
--   $$|\overline C_p(\Phi)-\overline C_p(\Psi)|\le2\varepsilon\ln d+2g(\varepsilon).$$
--   The false printed all-epsilon exact private-capacity witness is separately deferred. This statement retains both valid continuity bounds.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 37, Proposition 10: finite-input private-capacity continuity bounds

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

/-- arXiv:2304.05388v3, Proposition 10 bounds ONLY, PDF p.37. The false
printed all-epsilon private-capacity sharpness claim is deferred separately. -/
theorem proposition_10 {A B E : Type} [Fintype A] [Countable B] [Countable E]
    [Nonempty A] [Nonempty B] [Nonempty E] (Phi Psi : Channel A B) (PhiC PsiC : Channel A E)
    (hPhi : Complementary Phi PhiC) (hPsi : Complementary Psi PsiC)
    (eps : ℝ) (heps : 0 ≤ eps)
    (hclose : halfTraceClassDiamondDistance Phi.val Psi.val ≤ ENNReal.ofReal eps ∨
      halfTraceClassDiamondDistance PhiC.val PsiC.val ≤ ENNReal.ofReal eps) :
    |oneShotPrivateCapacityNats Phi.val PhiC.val - oneShotPrivateCapacityNats Psi.val PsiC.val| ≤
      2 * eps * Real.log (Fintype.card A) + 2 * correctionG eps := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

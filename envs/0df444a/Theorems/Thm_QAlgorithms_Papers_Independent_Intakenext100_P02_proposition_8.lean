-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_proposition_8
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.proposition_8
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:38:48.630232+00:00
-- url     : https://prove2.me/theorems/98c507c3-25f5-49e6-a2a5-e3e28b217a1a
-- title:
--   Proposition 8: finite-input Holevo-capacity continuity
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   For finite input dimension $d\ge1$, $\varepsilon\ge0$, and channels $\Phi,\Psi$, either $\frac12\|\Phi-\Psi\|_\diamond\le\varepsilon$ or the same inequality for some pair of complements in one common environment implies finite Holevo capacities and
--
--   $$|\overline C(\Phi)-\overline C(\Psi)|\le\varepsilon\ln d+g(\varepsilon).$$
--   Capacity optimizes over all generalized ensembles. For every $d\ge2$, $\varepsilon\in[0,1]$, the erasure pair at $0,\varepsilon$ has both channel and complementary distances exactly $\varepsilon$ and capacity difference $\varepsilon\ln d$. The fixed-positive-epsilon witness ratio to the full bound tends to one with $d$.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 34, Proposition 8: finite-input Holevo-capacity continuity

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

/-- arXiv:2304.05388v3, Proposition 8, PDF p.34. Either the channels or
SOME chosen complements can be close; both exact distances occur in the witness. -/
theorem proposition_8 :
    (∀ (A B E : Type) [Fintype A] [Countable B] [Countable E]
      [Nonempty A] [Nonempty B] [Nonempty E]
      (Phi Psi : Channel A B) (PhiC PsiC : Channel A E),
      Complementary Phi PhiC → Complementary Psi PsiC →
      ∀ eps : ℝ, 0 ≤ eps →
        (halfTraceClassDiamondDistance Phi.val Psi.val ≤ ENNReal.ofReal eps ∨
          halfTraceClassDiamondDistance PhiC.val PsiC.val ≤ ENNReal.ofReal eps) →
        CapacityComparison Phi.val Psi.val (eps * Real.log (Fintype.card A) + correctionG eps)) ∧
    (∀ (d : ℕ) (eps : ℝ), 2 ≤ d → 0 ≤ eps → eps ≤ 1 →
      ∃ Phi Psi PhiC PsiC : Channel (Fin d) (Option (Fin d)),
        IsErasureWitness Phi Psi PhiC PsiC eps ∧
        halfTraceClassDiamondDistance Phi.val Psi.val = ENNReal.ofReal eps ∧
        halfTraceClassDiamondDistance PhiC.val PsiC.val = ENNReal.ofReal eps ∧
        |(generalizedHolevoCapacity Phi.val).toReal - (generalizedHolevoCapacity Psi.val).toReal| = eps * Real.log d) ∧
    (∀ eps : ℝ, 0 < eps → eps ≤ 1 → Tendsto
      (fun d : ℕ => (eps * Real.log d) / (eps * Real.log d + correctionG eps)) atTop (𝓝 1)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

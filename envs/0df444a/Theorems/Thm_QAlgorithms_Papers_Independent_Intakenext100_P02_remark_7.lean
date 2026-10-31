-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_remark_7
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.remark_7
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:39:31.570434+00:00
-- url     : https://prove2.me/theorems/16bb11f3-8854-4a55-9e70-18198e3054c9
-- title:
--   Remark 7: necessity of the g term with complementary distance
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   On a two-dimensional space with any orthonormal basis, let $\Phi$ reset to the first basis vector and let $\Psi$ dephase in that basis. The identity channel complements $\Phi$, while $\Psi$ complements itself. Then
--
--   $$\|\Phi-\Psi\|_\diamond=2,\quad\|\mathrm{Id}-\Psi\|_\diamond=1,\quad\overline C(\Phi)=0,\quad\overline C(\Psi)=\ln2.$$
--   The resulting bounds are $3\ln2$ and $\ln2+\frac32\ln(3/2)$, with the second strictly smaller. The actual difference $\ln2$ exceeds $\frac12\ln2$, so the complementary-distance bound cannot omit $g$.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 35, Remark 7: necessity of the g term with complementary distance

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

/-- arXiv:2304.05388v3, Remark 7, PDF p.35. Exact distances are HALF the
printed norms 2 and 1. The final strict inequality disproves deleting g. -/
theorem remark_7 (b : HilbertBasis (Fin 2) ℂ (Hilbert (Fin 2))) :
    (∃ (Phi Psi Id : Channel (Fin 2) (Fin 2)),
      (∀ X, IsTraceClass X → Phi.val X = resetQubit b X ∧
        Psi.val X = basisDephasingCoefficients b X ∧ Id.val X = X) ∧
      Complementary Phi Id ∧ Complementary Psi Psi) ∧
    halfTraceClassDiamondDistance (resetQubit b) (basisDephasingCoefficients b) = 1 ∧
    halfTraceClassDiamondDistance id (basisDephasingCoefficients b) = 1/2 ∧
    generalizedHolevoCapacity (resetQubit b) = 0 ∧ generalizedHolevoCapacity (basisDephasingCoefficients b) = ENNReal.ofReal (Real.log 2) ∧
    Real.log 2 + correctionG 1 = 3 * Real.log 2 ∧
    (1/2 : ℝ) * Real.log 2 + correctionG (1/2) = Real.log 2 + (3/2 : ℝ) * Real.log (3/2) ∧
    (1/2 : ℝ) * Real.log 2 + correctionG (1/2) < Real.log 2 + correctionG 1 ∧
    (halfTraceClassDiamondDistance id (basisDephasingCoefficients b)).toReal * Real.log 2 <
      |(generalizedHolevoCapacity (resetQubit b)).toReal - (generalizedHolevoCapacity (basisDephasingCoefficients b)).toReal| := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

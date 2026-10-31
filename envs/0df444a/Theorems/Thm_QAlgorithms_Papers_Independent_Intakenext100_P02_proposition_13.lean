-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_proposition_13
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.proposition_13
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:47:03.008339+00:00
-- url     : https://prove2.me/theorems/50a9c031-f847-4635-9fb6-5f169682b680
-- title:
--   Proposition 13: Holevo-capacity lower bound from complementary q-c proximity
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   Let $d=\dim H_A<\infty$, $R\cong A$, and let $\widehat\Phi$ complement $\Phi$. Let $\mathcal S_m$ be all maximally entangled pure $AR$ states and let $\mathcal C$ contain every uniform q-c $ER$ state $d^{-1}\sum_i\rho_i\otimes|i\rangle\langle i|$, with arbitrary reference basis. Define $\varepsilon=\inf_{\omega\in\mathcal S_m}\inf_{\theta\in\mathcal C}\frac12\|(\widehat\Phi\otimes\mathrm{Id})(\omega)-\theta\|_1$. Then $0\le\varepsilon\le1$, the capacity is finite, and
--
--   $$\overline C(\Phi)\ge(1-\varepsilon)\ln d-g(\varepsilon).$$
--   The same lower bound holds using the actual distance of any specified pair $\omega,\theta$. No minimizing pair is assumed to exist.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 41, Proposition 13: Holevo-capacity lower bound from complementary q-c proximity

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

/-- arXiv:2304.05388v3, Proposition 13 and its note, PDF pp.41–42. Neither
infimum is assumed attained; the same bound holds for ANY specified pair. -/
theorem proposition_13 {A B E : Type} [Fintype A] [Countable B] [Countable E]
    [Nonempty A] [Nonempty B] [Nonempty E] (Phi : Channel A B) (PhiC : Channel A E)
    (hcomp : Complementary Phi PhiC) :
    0 ≤ qcProximity PhiC.val ∧ qcProximity PhiC.val ≤ 1 ∧ generalizedHolevoCapacity Phi.val < ⊤ ∧
    (1 - qcProximity PhiC.val) * Real.log (Fintype.card A) - correctionG (qcProximity PhiC.val) ≤
      (generalizedHolevoCapacity Phi.val).toReal ∧
    (∀ (psi : PureState (A × A)) (theta : State (E × A)),
      MaximallyEntangled psi → UniformQC theta.coefficients →
      let eps := (traceSize (tensorApply PhiC.val psi.val.coefficients - theta.coefficients)).toReal / 2
      (1-eps) * Real.log (Fintype.card A) - correctionG eps ≤ (generalizedHolevoCapacity Phi.val).toReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

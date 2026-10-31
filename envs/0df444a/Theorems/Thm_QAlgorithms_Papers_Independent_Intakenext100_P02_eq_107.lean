-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_eq_107
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.eq_107
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:41:59.57899+00:00
-- url     : https://prove2.me/theorems/31da7b25-4671-4189-899f-820180e0b3e0
-- title:
--   Holevo-loss bound by channel mutual-information loss (107)
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   Assume only that $I(\Psi\circ\Phi,\overline\rho(\mu))<\infty$. The downstream Holevo quantity is then finite and
--
--   $$0\le\chi(\Phi(\mu))-\chi(\Psi\circ\Phi(\mu))\le I(\Phi,\overline\rho(\mu))-I(\Psi\circ\Phi,\overline\rho(\mu))\le\infty.$$
--   The upstream Holevo quantity may be infinite. The first order comparison records nonnegativity before extended subtraction, preserving the full natural domain.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 39, Holevo-loss bound by channel mutual-information loss (107)

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

/-- arXiv:2304.05388v3, (107), PDF p.39. Only the downstream MI must be finite. -/
theorem eq_107 {A B C : Type} [Countable A] [Countable B] [Countable C]
    [Nonempty A] [Nonempty B] [Nonempty C] (Phi : Channel A B) (Psi : Channel B C)
    (mu : GeneralizedEnsemble A)
    (hfinite : mutualInformation (averageCoefficients mu) (Psi.val ∘ Phi.val) < ⊤) :
    ensembleHolevo (Psi.val ∘ Phi.val) mu < ⊤ ∧
    ensembleHolevo (Psi.val ∘ Phi.val) mu ≤ ensembleHolevo Phi.val mu ∧
    ensembleHolevo Phi.val mu - ensembleHolevo (Psi.val ∘ Phi.val) mu ≤
      mutualInformation (averageCoefficients mu) Phi.val -
        mutualInformation (averageCoefficients mu) (Psi.val ∘ Phi.val) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

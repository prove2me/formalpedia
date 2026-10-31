-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_eq_109
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.eq_109
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:44:09.504682+00:00
-- url     : https://prove2.me/theorems/ff8fd7aa-4a14-42be-8b96-042c8d08a25b
-- title:
--   Complementary output Holevo information increases under concatenation (109)
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   For every discrete ensemble and composable channels, with complements arising from actual Stinespring dilations,
--
--   $$\chi(\widehat{\Psi\circ\Phi}(\mu))\ge\chi(\widehat\Phi(\mu)).$$
--   The composite channel is tied to the actual composition on all trace-class inputs. The complementary environments may differ and both quantities may be infinite. This records the increase of complementary output Holevo information.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 40, Complementary output Holevo information increases under concatenation (109)

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

/-- arXiv:2304.05388v3, (109), PDF p.40. Complements can have unrelated
output environments; each is linked to its channel by an actual common dilation. -/
theorem eq_109 {A B C E F : Type} [Countable A] [Countable B] [Countable C]
    [Countable E] [Countable F] [Nonempty A] [Nonempty B] [Nonempty C]
    [Nonempty E] [Nonempty F] (Phi : Channel A B) (Psi : Channel B C)
    (Theta : Channel A C) (hTheta : ∀ X, IsTraceClass X → Theta.val X = Psi.val (Phi.val X))
    (PhiC : Channel A E) (ThetaC : Channel A F)
    (hcompPhi : Complementary Phi PhiC) (hcompTheta : Complementary Theta ThetaC)
    (mu : CountableStateEnsemble A) :
    (∑' n, mu.weight n * extendedRelativeEntropyNats
      (PhiC.val (mu.state n).coefficients)
      (PhiC.val (fun i j => ∑' n, ((mu.weight n).toReal : ℂ) * (mu.state n).coefficients i j))) ≤
    (∑' n, mu.weight n * extendedRelativeEntropyNats
      (ThetaC.val (mu.state n).coefficients)
      (ThetaC.val (fun i j => ∑' n, ((mu.weight n).toReal : ℂ) * (mu.state n).coefficients i j))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_entropy_exchange_monotonicity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.entropy_exchange_monotonicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:44:57.257999+00:00
-- url     : https://prove2.me/theorems/6302ced9-d675-42d0-91ed-215878db9691
-- title:
--   Unnumbered p.40: entropy-exchange monotonicity
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   Let $\Phi:A\to B$ and $\Psi:B\to C$. Suppose $S(\Psi(\sigma))\ge S(\sigma)$ for every normalized state $\sigma$ of $B$. Then for every input state, with entropy exchange defined by a complementary output,
--
--   $$S(\widehat{\Psi\circ\Phi}(\rho))\ge S(\widehat\Phi(\rho)).$$
--   The hypothesis is universal on $B$, not merely at $\Phi(\rho)$. Infinite entropies are allowed and no energy bound is imposed.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 40, Unnumbered p.40: entropy-exchange monotonicity

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

/-- arXiv:2304.05388v3, unnumbered entropy-exchange monotonicity, PDF p.40.
The entropy-nondecrease hypothesis holds on EVERY B state. -/
theorem entropy_exchange_monotonicity {A B C E F : Type}
    [Countable A] [Countable B] [Countable C] [Countable E] [Countable F]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty F]
    (Phi : Channel A B) (Psi : Channel B C) (Theta : Channel A C)
    (hTheta : ∀ X, IsTraceClass X → Theta.val X = Psi.val (Phi.val X))
    (PhiC : Channel A E) (ThetaC : Channel A F)
    (hcompPhi : Complementary Phi PhiC) (hcompTheta : Complementary Theta ThetaC)
    (hPsi : ∀ sigma : State B, extendedEntropyNats sigma.coefficients ≤
      extendedEntropyNats (Psi.val sigma.coefficients)) (rho : State A) :
    extendedEntropyNats (PhiC.val rho.coefficients) ≤
      extendedEntropyNats (ThetaC.val rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

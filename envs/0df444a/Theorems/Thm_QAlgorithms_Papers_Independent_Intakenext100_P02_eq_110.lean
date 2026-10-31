-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_eq_110
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.eq_110
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:45:38.05949+00:00
-- url     : https://prove2.me/theorems/deae8b1a-2c6f-43ab-b60a-d3d9073908ae
-- title:
--   Capacity deficit as complementary discord (110)
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   For $S(\rho)<\infty$, any channel and complement, and any given purification $\widehat\rho_{AR}$,
--
--   $$S(\rho)-\overline C(\Phi,\rho)=I(\widehat\Phi,\rho)-\overline C(\widehat\Phi,\rho)=D_R((\widehat\Phi\otimes\mathrm{Id}_R)(\widehat\rho)).$$
--   Only the input entropy is required finite. This identifies the capacity deficit with complementary output discord.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 41, Capacity deficit as complementary discord (110)

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

/-- arXiv:2304.05388v3, (110), PDF p.41. Finite INPUT entropy suffices. -/
theorem eq_110 {A B E R : Type} [Countable A] [Countable B] [Countable E] [Countable R]
    [Nonempty A] [Nonempty B] [Nonempty E] [Nonempty R]
    (Phi : Channel A B) (PhiC : Channel A E) (hcomp : Complementary Phi PhiC)
    (rho : State A) (psi : PureState (A × R)) (hpsi : Purifies psi rho.coefficients)
    (hfinite : extendedEntropyNats rho.coefficients < ⊤) :
    extendedEntropyNats rho.coefficients - barycentricChi rho.coefficients Phi.val =
      constrainedInformationDeficit PhiC.val rho.coefficients ∧
    constrainedInformationDeficit PhiC.val rho.coefficients = discreteOptimizedDiscord (tensorApply PhiC.val psi.val.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

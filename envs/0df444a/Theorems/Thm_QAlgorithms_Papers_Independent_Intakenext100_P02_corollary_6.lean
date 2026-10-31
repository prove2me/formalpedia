-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_corollary_6
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.corollary_6
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:30:36.899844+00:00
-- url     : https://prove2.me/theorems/279375e8-641a-4462-aeb5-1ae2559b63b3
-- title:
--   Corollary 6: extended measurement-discord entropy lower bound
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   If $M$ is rank one and $S(\omega)<\infty$, then
--
--   $$S(\omega_B)\le\widehat D_B^M(\omega)+S(\omega).$$
--   This is the printed lower bound $\widehat D_B^M\ge S(\omega_B)-S(\omega)$ written additively. The marginal entropy may be infinite.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 23, Corollary 6: extended measurement-discord entropy lower bound

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

/-- arXiv:2304.05388v3, Corollary 6, PDF p.23. Finite total entropy; marginal
entropy may be infinite. Additive form avoids an extended subtraction. -/
theorem corollary_6 {A B K : Type} [Countable A] [Countable B]
    [Nonempty A] [Nonempty B] [Countable K] (M : DiscretePOVM B K)
    (hM : HasRankOneEffects M) (omega : State (A × B))
    (hfinite : extendedEntropyNats omega.coefficients < ⊤) :
    extendedEntropyNats (traceFirst omega.coefficients) ≤
      extendedDiscordM M omega.coefficients + extendedEntropyNats omega.coefficients := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

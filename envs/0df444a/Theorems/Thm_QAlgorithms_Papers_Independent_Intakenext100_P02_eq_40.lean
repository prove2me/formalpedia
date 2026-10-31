-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_eq_40
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.eq_40
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:19:21.671616+00:00
-- url     : https://prove2.me/theorems/99686a42-c24a-4deb-8993-f9c847bccc4a
-- title:
--   Unoptimized Koashi–Winter identity (40)
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   For any state $\omega_{ABC}$ and discrete $M=\{M_i\}$ on $B$, form $p_i=\operatorname{Tr}M_i\omega_B$ and $\rho_i=p_i^{-1}\operatorname{Tr}_B[(I_A\otimes M_i\otimes I_C)\omega]$, omitting zero weights. With $\Theta_A$ the partial trace $AC\to A$,
--
--   $$C_B^M(\omega_{AB})=\chi(\Theta_A(\{p_i,\rho_i\}))=\sum_{i:p_i>0}p_iD((\rho_i)_A\Vert\omega_A).$$
--   The ensemble and its normalizations are computed from the state and effects. This is the unoptimized correlation identity.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 15, Unoptimized Koashi–Winter identity (40)

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

/-- arXiv:2304.05388v3, unoptimized relation (40), PDF p.15. -/
theorem eq_40 {A B C K : Type} [Countable A] [Countable B] [Countable C]
    [Nonempty A] [Nonempty B] [Nonempty C] [Countable K]
    (omega : State ((A × B) × C)) (M : DiscretePOVM B K) :
    classicalM M (traceSecond omega.coefficients) = conditionalHolevoA M omega.coefficients := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

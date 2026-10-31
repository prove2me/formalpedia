-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_proposition_3
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.proposition_3
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:24:40.618423+00:00
-- url     : https://prove2.me/theorems/ae491359-4f5f-4820-947f-59674cc16cad
-- title:
--   Proposition 3: zero discord is quantum-classical under either finite-entropy condition (abstract seed)
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   Let $\omega_{AB}$ have $C_B(\omega)<\infty$. If either $S(\omega)<\infty$ or $S(\omega_B)<\infty$, then
--
--   $$D_B(\omega)=0\quad\Longrightarrow\quad\omega=\sum_i p_i\rho_i\otimes|i\rangle\langle i|$$
--   for some probability distribution, normalized states of $A$, and complete orthonormal basis of $B$. The entropy hypotheses are alternatives. This is the proved infinite-dimensional zero-discord characterization on its natural domain.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 19, Proposition 3: zero discord is quantum-classical under either finite-entropy condition (abstract seed)

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

/-- arXiv:2304.05388v3, Proposition 3, PDF pp.19–20 (abstract p.1).
Either entropy is finite; the natural discord domain is explicit. -/
theorem proposition_3 {A B : Type} [Countable A] [Countable B]
    [Nonempty A] [Nonempty B] (omega : State (A × B))
    (hdomain : discreteClassicalCorrelation omega.coefficients < ⊤)
    (hfinite : extendedEntropyNats omega.coefficients < ⊤ ∨
      extendedEntropyNats (traceFirst omega.coefficients) < ⊤)
    (hzero : discreteOptimizedDiscord omega.coefficients = 0) : IsQC omega.coefficients := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

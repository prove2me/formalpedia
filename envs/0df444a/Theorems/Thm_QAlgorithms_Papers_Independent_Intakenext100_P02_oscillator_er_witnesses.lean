-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_oscillator_er_witnesses
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.oscillator_er_witnesses
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:16:27.571625+00:00
-- url     : https://prove2.me/theorems/b4c37d70-4fa0-437b-9516-e871ff8c58bf
-- title:
--   Unnumbered p.12 and Remark 3: oscillator entropy-reduction witnesses
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   For an $\ell$-mode oscillator, $\ell\ge1$, let the positive energy quanta be $a_i=\hbar\omega_i$ and let $H=\sum_i a_iN_i$ be its grounded Hamiltonian. Let $\gamma_H(E)$ be the normalized Gibbs state of mean energy $E\ge0$, using the vacuum at $E=0$, and let $F_H$ denote the constrained entropy supremum. For every state $\rho$ of $A$ and every rank-one discrete POVM on the oscillator,
--
--   $$R_M(\rho\otimes\gamma_H(E))=S(\gamma_H(E))=F_H(E).$$
--   Moreover $G(E)/F_H(E)\to1$ as $E\to\infty$, where $G(E)=\ell\ln((E+\sum_i a_i)/(\ell(\prod_i a_i)^{1/\ell}))+\ell$. These are the explicit witnesses; no external sharpness predicate is assumed.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 13, Unnumbered p.12 and Remark 3: oscillator entropy-reduction witnesses

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

open QAlgorithms.Papers.Independent.Claimed50.P13 (PositiveObservable closedFormExpectation)

open QAlgorithms.Papers.Independent.Frontier18.P18 (stateSquareRoot)

/-- arXiv:2304.05388v3, unnumbered p.12 and Remark 3, PDF pp.12–13.
Explicit Gibbs attaining family and G(E)/F_H(E)→1. No unspecified external
asymptotic-tightness predicate is asserted. -/
theorem oscillator_er_witnesses {A : Type} [Countable A] [Nonempty A]
    {l : ℕ} (hl : 0 < l) (frequency : Fin l → ℝ) (hf : ∀ i, 0 < frequency i) :
    (∀ (K : Type) [Countable K] (M : DiscretePOVM (Fin l → ℕ) K), HasRankOneEffects M →
      ∀ (rho : State A) (E : ℝ), 0 ≤ E →
        IsDensity (oscillatorGibbs frequency hf E) ∧
        localER M (productCoeff rho.coefficients (oscillatorGibbs frequency hf E)) =
          extendedEntropyNats (oscillatorGibbs frequency hf E) ∧
        extendedEntropyNats (oscillatorGibbs frequency hf E) = oscillatorEntropySupremum frequency hf E) ∧
    Tendsto (fun E : ℝ => oscillatorG frequency E / (oscillatorEntropySupremum frequency hf E).toReal)
      atTop (𝓝 1) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

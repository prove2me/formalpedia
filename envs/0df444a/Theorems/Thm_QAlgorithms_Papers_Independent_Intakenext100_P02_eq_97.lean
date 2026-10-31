-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P02_eq_97
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P02.eq_97
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:37:56.919986+00:00
-- url     : https://prove2.me/theorems/94d50471-2f6f-495d-bc56-26e02809aaf2
-- title:
--   Explicit oscillator privacy erasure witnesses (97)
-- statement:
--   All systems are nonzero separable complex Hilbert spaces, including finite systems. States are positive trace-class operators of trace one; state convergence uses trace norm. Entropies and relative entropies use natural logarithms and may be $+\infty$. A discrete POVM may have finitely or countably many outcomes. Write $S$ for von Neumann entropy, $I(A:B)$ for quantum mutual information, $C_B^M,C_B$ for the fixed-measurement and optimized one-way classical correlations, and $D_B^M,D_B$ for their discord deficits on their natural finite-classical-correlation domains. Write $R_M(\omega)=\mathrm{ER}(\omega,I_A\otimes M)$; $h_2(p)=-p\ln p-(1-p)\ln(1-p)$ and $g(x)=(x+1)\ln(x+1)-x\ln x$, with zero endpoint terms understood as zero.
--
--   For every pure-state ensemble of an $\ell$-mode grounded oscillator, $\ell\ge1$, with positive energy quanta $\hbar\omega_i$, with computed Gibbs average $\gamma_H(E)$, $E\ge0$, and all erasure probabilities $p,q\in[0,1]$, the Holevo terms are finite and
--
--   $$|\pi(\Omega_p,\mu)-\pi(\Omega_q,\mu)|=2|p-q|\chi(\mu)=2|p-q|S(\gamma_H(E))=2|p-q|F_H(E).$$
--   Here privacy is the signed difference of receiver and complementary Holevo information, not an optimized private capacity. This preserves the exact witness for the full probability interval.
--
--   Here $H=\sum_i\hbar\omega_iN_i$, $F_H(E)=\sup_{\operatorname{Tr}H\tau\le E}S(\tau)$, and $\gamma_H(E)$ is the actual normalized Gibbs density, with the vacuum used at $E=0$.
-- source:
--   Correlation measures of a quantum state and information characteristics of a quantum channel, arXiv:2304.05388v3, PDF p. 33, Explicit oscillator privacy erasure witnesses (97)

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

/-- arXiv:2304.05388v3, exact SIGNED ensemble-privacy witnesses (97), PDF p.33.
These are not the truncated, nonnegative optimized private capacities. -/
theorem eq_97 {l : ℕ} (hl : 0 < l) (frequency : Fin l → ℝ) (hf : ∀ i, 0 < frequency i)
    (E p q : ℝ) (hE : 0 ≤ E) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (mu : GeneralizedEnsemble (Fin l → ℕ))
    (hpure : (mu : Measure (State (Fin l → ℕ))).support ⊆ pureStates (Fin l → ℕ))
    (haverage : averageCoefficients mu = oscillatorGibbs frequency hf E) :
    ensembleHolevo id mu < ⊤ ∧ oscillatorEntropySupremum frequency hf E < ⊤ ∧
    (∀ r ∈ ({p,q,1-p,1-q} : Set ℝ), ensembleHolevo (flaggedTraceClassErasure r) mu < ⊤) ∧
    |privacy (flaggedTraceClassErasure p) (flaggedTraceClassErasure (1-p)) mu - privacy (flaggedTraceClassErasure q) (flaggedTraceClassErasure (1-q)) mu| =
      2 * |p-q| * (ensembleHolevo id mu).toReal ∧
    2 * |p-q| * (ensembleHolevo id mu).toReal =
      2 * |p-q| * (extendedEntropyNats (oscillatorGibbs frequency hf E)).toReal ∧
    2 * |p-q| * (extendedEntropyNats (oscillatorGibbs frequency hf E)).toReal =
      2 * |p-q| * (oscillatorEntropySupremum frequency hf E).toReal := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P02

end

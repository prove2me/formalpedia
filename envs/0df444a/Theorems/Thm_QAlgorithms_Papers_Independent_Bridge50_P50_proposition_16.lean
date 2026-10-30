-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_proposition_16
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.proposition_16
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:32:15.13724+00:00
-- url     : https://prove2.me/theorems/2952afcd-87e3-44c9-bf19-d422bf9af02f
-- title:
--   Proposition 16: proposition 16
-- statement:
--   Let $\mathcal S$ be the density operators on a nonzero, finite-dimensional complex Hilbert space of dimension $d$. Logarithms are in bits, $D$ is support-aware Umegaki relative entropy, and $V$ is relative entropy variance in bits squared. Let $S\subseteq\mathcal S$ be arbitrary, $\lambda_0>0$, $0<\varepsilon<1$, and $|\varepsilon_n-\varepsilon|\le n^{-1/2}$ for positive $n$. Set $\varepsilon_* =\min(\varepsilon,1-\varepsilon)$. For a sequence $\rho^n=\bigotimes_i\rho_i$ with $\rho_i\in S$, put $I_n(\sigma)=n^{-1}\sum_iD(\rho_i\|\sigma)$ and $V_n(\sigma)=n^{-1}\sum_iV(\rho_i\|\sigma)$.
--
--   There are $L_1>3$, $K_1>0$ and $N_1\ge2$, chosen before $n,\sigma,\rho^n$, such that for $n\ge N_1$ and every state $\sigma$ with $\lambda_{\min}(\sigma)\ge\lambda_0$,
--   $$
--   \left|D_h^{\varepsilon_n}(\rho^n\|\sigma^{\otimes n})-nI_n(\sigma)\right|
--   \le\sqrt{nV_n(\sigma)/\varepsilon_*}+L_1\log_2n\le K_1\sqrt n.
--   $$
--   For each fixed $\xi>0$ and full-rank $\sigma$, there are $L_2>3,N_2\ge2$, before all permitted sequences, such that whenever $n\ge N_2$ and $V_n(\sigma)\ge\xi$,
--   $$
--   \left|D_h^{\varepsilon_n}(\rho^n\|\sigma^{\otimes n})-nI_n(\sigma)-\sqrt{nV_n(\sigma)}\Phi^{-1}(\varepsilon)\right|\le L_2\log_2 n.
--   $$
--   If $\sigma=\bar\rho_n=n^{-1}\sum_i\rho_i$, the same bound has constants $L_3>3,N_3\ge2$ depending only on the fixed data and $\xi$, before all sequences; no fixed positive lower eigenvalue of $\bar\rho_n$ is required. The variance condition remains.
--
--   These are two-sided estimates uniform over nonidentical product-state sequences. The fixed error sequence is quantified before the constants.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 17, Proposition 16

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P50

noncomputable section

open scoped Topology BigOperators ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Bridge50.P50

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted primitives; these names do not create local declarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat logTwo testingBeta normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage)

open QAlgorithms.Papers.Independent.Information100.P69 (entropy)

open QAlgorithms.Papers.Independent.Dependency50.P35 (Dominates)

open QAlgorithms.Papers.Independent.Dependency50.P36 (pairInformationVariance)

open QAlgorithms (vnEntropy traceDistance minEigenvalue)

attribute [local instance] QAlgorithms.Papers.Independent.Bridge50.P50.matrixBorelMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Bridge50.P50.matrixBorelSpace

/-- Proposition 16, PDF pp.17,28–29: BOTH bounds have absolute values. All constants
precede the sequences they control. The last clause needs no fixed lower spectral bound
on the empirical barycenter; the positive variance condition remains.
The final clause's general-S proof interface with finite Lemma 29 is recorded in the audit. -/
theorem proposition_16 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (S : Set (Mat I)) (hS : ∀ rho ∈ S, QAlgorithms.IsDensityMatrix rho)
    (e l0 : ℝ) (he : 0 < e ∧ e < 1) (hl0 : 0 < l0)
    (es : ℕ → ℝ) (hes : ErrorEnvelope e es) :
    (∃ L1 K1 : ℝ, 3 < L1 ∧ 0 < K1 ∧ ∃ N1 : ℕ, 2 ≤ N1 ∧
      ∀ n : ℕ, N1 ≤ n → ∀ sigma : Mat I, QAlgorithms.IsDensityMatrix sigma →
      l0 ≤ minEigenvalue sigma → ∀ rho : Fin n → Mat I, (∀ i, rho i ∈ S) →
      |(normalizedTestingDivergence (es n) (tensorWord rho) (tensorWord (fun _ => sigma))).toReal -
          n * empiricalInformation rho sigma| ≤
        Real.sqrt (n * empiricalVariance rho sigma / min e (1-e)) + L1 * logTwo n ∧
      Real.sqrt (n * empiricalVariance rho sigma / min e (1-e)) + L1 * logTwo n ≤ K1 * Real.sqrt n) ∧
    (∀ xi : ℝ, 0 < xi → ∀ sigma : Mat I, QAlgorithms.IsDensityMatrix sigma →
      0 < minEigenvalue sigma → ∃ L2 : ℝ, 3 < L2 ∧ ∃ N2 : ℕ, 2 ≤ N2 ∧
      ∀ n : ℕ, N2 ≤ n → ∀ rho : Fin n → Mat I, (∀ i, rho i ∈ S) →
      xi ≤ empiricalVariance rho sigma →
      |(normalizedTestingDivergence (es n) (tensorWord rho) (tensorWord (fun _ => sigma))).toReal -
        n * empiricalInformation rho sigma -
        Real.sqrt (n * empiricalVariance rho sigma) * normalQuantile e| ≤ L2 * logTwo n) ∧
    (∀ xi : ℝ, 0 < xi → ∃ L3 : ℝ, 3 < L3 ∧ ∃ N3 : ℕ, 2 ≤ N3 ∧
      ∀ n : ℕ, N3 ≤ n → ∀ rho : Fin n → Mat I, (∀ i, rho i ∈ S) →
      xi ≤ empiricalVariance rho (empiricalBarycenter rho) →
      |(normalizedTestingDivergence (es n) (tensorWord rho)
          (tensorWord (fun _ => empiricalBarycenter rho))).toReal -
        n * empiricalInformation rho (empiricalBarycenter rho) -
        Real.sqrt (n * empiricalVariance rho (empiricalBarycenter rho)) * normalQuantile e| ≤ L3 * logTwo n) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P66_simultaneousReducedInformal
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P66.simultaneousReducedInformal
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:44:21.07681+00:00
-- url     : https://prove2.me/theorems/62355261-5c88-4092-a44f-c8729916b997
-- title:
--   Simultaneous normalized reduced-process tomography
-- statement:
--   Let $\mathcal E$ be any CPTP map on $n\ge1$ qubits, and let $\rho_{\Lambda}=2^{-n}\Lambda_{\mathcal E}$ be its trace-one reference-first Choi state. For $0\le k\le n$, let $\rho_{\Lambda,S}$ retain the reference and output copies of a $k$-element physical subsystem $S$, tracing out both complements. Fix $0<\epsilon,\delta<1$.
--
--   There is an absolute $C>0$, uniform over all these data, such that the following independent fresh-shot counts suffice to estimate every $\rho_{\Lambda,S}$ with one simultaneous success event of probability at least $1-\delta$ in the indicated norm:
--
--   $$
--   \begin{array}{ll}
--   \text{global Clifford, Frobenius:}&\left\lceil C4^{n+k}\epsilon^{-2}\log(2(8n)^{2k}/\delta)\right\rceil,\\
--   \text{Pauli-6, Frobenius:}&\left\lceil C36^k\epsilon^{-2}\log(2(8n)^{2k}/\delta)\right\rceil,\\
--   \text{Pauli-6, trace:}&\left\lceil C144^k\epsilon^{-2}\log((24n)^{2k}/\delta)\right\rceil.
--   \end{array}
--   $$
--
--   The trace norm has no extra factor $1/2$. At $k=0$ the scalar marginal $1$ requires no samples. For fixed $k,\epsilon,\delta$, a Pauli-6 count $N\le D_{k,\epsilon,\delta}\log(2n)$ suffices for either norm, uniformly in $n$ and the process. Each estimator is chosen before the unknown process. The reduced channel has a maximally mixed complementary input.
--
--   This is a quantum sample guarantee, including full tomography at $k=n$, without a unitarity promise or a total classical runtime bound.
-- source:
--   Classical Shadows for Quantum Process Tomography on Near-term Quantum Computers, arXiv:2110.02965v3, PDF p. 2, Theorem II.1 (informal)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P66

noncomputable section

open MeasureTheory QAlgorithms ClassicalShadows

open scoped Matrix ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Intakethird100.P66

attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Theorem II.1 (informal), PDF p.2, with A.3 p.14: all three
norm/ensemble clauses and the fixed-k logarithmic sample consequence.
Constants precede system size, accuracy, confidence, and unknown process. -/
theorem simultaneousReducedInformal [∀ m : ℕ, Fintype (Clifford.ProjectiveGroup m)] :
    (∃ C : ℝ, 0 < C ∧ ∀ (n k : ℕ), 0 < n → k ≤ n →
      ∀ (eps delta : ℝ), 0 < eps → eps < 1 → 0 < delta → delta < 1 →
        ReducedRecovers (globalFrame (n + n)) k
          (sampleCount k (C * (4 : ℝ) ^ (n + k) / eps ^ 2 * reducedLog n k delta))
          .frobenius eps delta ∧
        ReducedRecovers (pauliFrame (n + n)) k
          (sampleCount k (C * (36 : ℝ) ^ k / eps ^ 2 * reducedLog n k delta))
          .frobenius eps delta ∧
        ReducedRecovers (pauliFrame (n + n)) k
          (sampleCount k (C * (144 : ℝ) ^ k / eps ^ 2 * traceSampleLog n k delta))
          .trace eps delta) ∧
    (∀ (k : ℕ) (eps delta : ℝ), 0 < eps → eps < 1 → 0 < delta → delta < 1 →
      ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 0 < n → k ≤ n →
        ∃ N : ℕ, (N : ℝ) ≤ D * Real.log (2 * (n : ℝ)) ∧
          ReducedRecovers (pauliFrame (n + n)) k N .frobenius eps delta ∧
          ReducedRecovers (pauliFrame (n + n)) k N .trace eps delta) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P66

end

-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapL14_lowRankTomography_exact
-- name    : QAlgorithms.Papers.RoadmapL14.lowRankTomography_exact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:22:18.816906+00:00
-- url     : https://prove2.me/theorems/51c874bc-bc3b-41db-b008-e46b4954aed1
-- title:
--   Low-rank tomography: exact recovery by random Pauli expectations
-- statement:
--   Let \(n\ge 0\) be the number of qubits, \(d=2^n\), and let \(\rho\in\mathbb C^{d\times d}\) be a fixed density matrix (positive semidefinite with trace one) of exact rank \(r\). There are absolute constants \(a,b,c_0>0\), independent of \(n,r,\rho\), such that the following holds for every \(c\ge c_0\).
--
--   Set \(m=\lceil cdr(\ln d)^2\rceil\). Independently sample \(m\) unphased Pauli strings \(w(A_i)\), uniformly with replacement from all \(d^2\) tensor products of \(I,X,Y,Z\), including the identity. Suppose their exact expectations \(y_i=\operatorname{Tr}(w(A_i)\rho)\) are known. Write \(\mathcal O(A,y)\) for the set of minimizers of
--   $$
--   \min_{\sigma=\sigma^\dagger}\|\sigma\|_{\mathrm{tr}}
--   \quad\text{subject to}\quad
--   \operatorname{Tr}\sigma=1,\qquad
--   \operatorname{Tr}(w(A_i)\sigma)=y_i\quad(1\le i\le m).
--   $$
--   The trace norm is the sum of the singular values; competitors need not be positive semidefinite and have no rank constraint. Then
--   $$
--   \Pr_A\!\left[\mathcal O(A,y)\ne\{\rho\}\right]\le a e^{-bc}.
--   $$
--   Thus this specific convex program attains its minimum uniquely at the unknown state with exponentially small failure probability. The probability is over the design for each fixed state, and \(m\) counts exact expectation settings, rather than physical copies or computation time.
--
--   **Formalization Note** Natural logarithms and integer rounding pin down the paper's asymptotic notation using its closing proof on PDF p.3. The sampling law and optimizer set are frozen definitions depending only on public \(n,m\), and on the design and supplied data, respectively. For \(n=0\), \(d=r=1\) and \(m=0\); trace one alone gives unique recovery.
-- source:
--   Quantum state tomography via compressed sensing, arXiv:0909.3304v4, Theorem 1 (Low-rank tomography), convex program (1), PDF p. 2. https://arxiv.org/abs/0909.3304v4 . PDF SHA-256: 617996f892b3fddb95fe7802660e3b22bd3c8635f77a27c5f0b9ae23ecb00486.

import Definitions.Def_QAlgorithms_Defs_ExactPauliRecovery
set_option autoImplicit false

noncomputable section

open scoped ENNReal ComplexOrder

namespace QAlgorithms.Papers.RoadmapL14

/-- Gross, Liu, Flammia, Becker and Eisert, *Quantum state tomography via compressed
sensing*, arXiv:0909.3304v4, PDF p.2, Theorem 1 and convex program (1); sampling
with replacement and the Hermitian optimization domain are specified on PDF pp.5-6.
For each fixed density matrix of exact rank `r`, `m` independent uniform unphased
Pauli expectations determine the unique trace-norm minimizer, except with probability
at most `a * exp (-b * c)`, for absolute positive constants and `c >= c0`.
Here `m = ceil (c * d * r * (ln d)^2)` and `d = 2^n`. The data are exact expectations;
the objective is the full trace norm and competitors have trace one and are Hermitian,
without a positivity or rank constraint. This counts settings, not copies or runtime. -/
theorem lowRankTomography_exact :
    ∃ a b c0 : ℝ, 0 < a ∧ 0 < b ∧ 0 < c0 ∧
      ∀ (n r : ℕ) (rho : Matrix (QAlgorithms.Qubits n) (QAlgorithms.Qubits n) ℂ),
      ∀ density : QAlgorithms.IsDensityMatrix rho, rho.rank = r →
      ∀ c : ℝ, c0 ≤ c →
        let d : ℕ := 2 ^ n
        let m : ℕ := ⌈c * (d : ℝ) * (r : ℝ) * Real.log (d : ℝ) ^ 2⌉₊
        (QAlgorithms.PauliDesign.uniformDesign n m).toOuterMeasure
          {A | QAlgorithms.LowRankTomography.optimizerSet A
            (QAlgorithms.PauliDesign.expectationData A rho density.1.isHermitian) ≠ {rho}} ≤
          ENNReal.ofReal (a * Real.exp (-b * c)) := by sorry

end QAlgorithms.Papers.RoadmapL14

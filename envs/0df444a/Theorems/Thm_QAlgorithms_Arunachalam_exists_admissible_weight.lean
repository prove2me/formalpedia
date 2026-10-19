-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_exists_admissible_weight
-- name    : QAlgorithms.Arunachalam.exists_admissible_weight
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:53:50.29009+00:00
-- url     : https://prove2.me/theorems/6e329f27-e5e4-494a-912a-b8307941bfd7
-- title:
--   An admissible weight k of order log M/(log(N/log M)+1)
-- statement:
--   This combinatorial fact (Kothari, Lemma 5) supplies a large admissible parameter for Lemma 6.4.8.
--
--   There is an absolute constant $c_0>0$ such that for all integers $N\ge 1$ and $M$ with $N<M\le 2^N$ there exists an integer $k$ with $1\le k\le N$,
--
--   $$
--   k\ \ge\ c_0\,\frac{\log_2 M}{\log_2\!\big(N/\log_2 M\big)+1}
--   \qquad\text{and}\qquad
--   \binom{N}{k-1}+\binom{N}{k}\le M .
--   $$
--
--   Since $\log_2 M\le N$, the denominator is at least $1$.
--
--   Combined with Lemma 6.4.8, this yields the quantum lower bound of Theorem 6.4.7 in the regime $N<M\le 2^N$.
--
--   **Formalization Note** The requirement $k\le N$ is part of the statement: without it any $k\ge N+2$ makes both binomial coefficients vanish and the fact becomes trivial. The degenerate case $N=0$ (which forces $M=1$) is excluded: there the range $1\le k\le N$ is empty. The extracted text prints the range as $N<M\le 2N$; the page reads $2^N$.
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 134, Fact 6.4.9. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_Learning
set_option autoImplicit false

namespace QAlgorithms.Arunachalam

open QAlgorithms.Learning


/-- Arunachalam p.134, Fact 6.4.9 (Kothari, Lemma 5): for every `N < M ≤ 2^N` there is a
Hamming-weight parameter `k ∈ [1, N]` with `k = Ω(log M / (log(N / log M) + 1))` and
`binom(N, k−1) + binom(N, k) ≤ M`. Logarithms are base 2; the constant of `Ω` is universal. The
text extraction prints the range as `N < M ≤ 2N`; the page reads `2^N`. The degenerate case
`N = 0` (forcing `M = 1`) is excluded by `1 ≤ N`: there the weight range `[1, N]` of
Lemma 6.4.8 is empty. -/
theorem exists_admissible_weight :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ N M : ℕ, 1 ≤ N → N < M → M ≤ 2 ^ N →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧
        c0 * (Real.logb 2 (M : ℝ) / (Real.logb 2 ((N : ℝ) / Real.logb 2 (M : ℝ)) + 1)) ≤ (k : ℝ) ∧
        N.choose (k - 1) + N.choose k ≤ M := by
  sorry


end QAlgorithms.Arunachalam

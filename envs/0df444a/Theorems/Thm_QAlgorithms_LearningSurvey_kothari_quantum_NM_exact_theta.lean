-- Prove2me | Theorems.Thm_QAlgorithms_LearningSurvey_kothari_quantum_NM_exact_theta
-- name    : QAlgorithms.LearningSurvey.kothari_quantum_NM_exact_theta
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:55:54.12044+00:00
-- url     : https://prove2.me/theorems/61e9405a-da91-43c1-a6e1-eef4b957421d
-- title:
--   Kothari: optimal quantum (N,M)-query complexity of exact learning
-- statement:
--   This is Kothari's tight characterization of the quantum $(N,M)$-query complexity of exact learning.
--
--   Let $N=2^n$. For an integer $M$, the quantum $(N,M)$-query complexity $Q(N,M)$ is the maximum, over concept classes $C\subseteq\{0,1\}^N$ with $|C|=M$, of the least number of queries to $O_c:|x,b\rangle\mapsto|x,b\oplus c(x)\rangle$ made by a quantum exact learner for $C$ (success probability at least $2/3$ on every target). There are absolute constants $c_1,c_2>0$ such that:
--
--   1. if $2\le M\le N$, then $c_1\sqrt M\le Q(N,M)\le c_2\sqrt M$;
--   2. if $N<M\le 2^N$, then, with $\log=\log_2$,
--   $$c_1\sqrt{\frac{N\log M}{\log(N/\log M)+1}}\ \le\ Q(N,M)\ \le\ c_2\sqrt{\frac{N\log M}{\log(N/\log M)+1}}.$$
--
--   Compared with the classical $\Theta(\min\{M,N\})$ of Theorem 4.5, it quantifies the quantum speed-up for oracle identification.
--
--   **Formalization Note** $M=1$ is excluded from the first case (a single concept needs no queries). In the second case $1<\log_2 M\le N$, so the denominator is at least $1$. Logarithms are base 2; another base changes the expression only by bounded factors.
-- source:
--   Srinivasan Arunachalam and Ronald de Wolf, A Survey of Quantum Learning Theory, 2017, v3, PDF p. 10, §4.1.2, Theorem 4.6. https://arxiv.org/pdf/1701.06806v3

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
set_option autoImplicit false

namespace QAlgorithms.LearningSurvey

universe u




/-- **Theorem 4.6** (Kothari; survey p.10). The quantum `(N, M)`-query complexity of exact
learning (`N = 2^n`) is `Θ(√M)` for `M ≤ N` and
`Θ(√(N log M / (log(N / log M) + 1)))` for `N < M ≤ 2^N` (logarithms base 2). -/
theorem kothari_quantum_NM_exact_theta :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (n M : ℕ),
      (2 ≤ M → M ≤ 2 ^ n →
        c₁ * Real.sqrt (M : ℝ) ≤ (Learning.quantumExactNM n M : ℝ) ∧
          (Learning.quantumExactNM n M : ℝ) ≤ c₂ * Real.sqrt (M : ℝ)) ∧
      (2 ^ n < M → M ≤ 2 ^ (2 ^ n) →
        c₁ * Real.sqrt (((2 ^ n : ℕ) : ℝ) * Real.logb 2 (M : ℝ) /
            (Real.logb 2 (((2 ^ n : ℕ) : ℝ) / Real.logb 2 (M : ℝ)) + 1)) ≤
          (Learning.quantumExactNM n M : ℝ) ∧
        (Learning.quantumExactNM n M : ℝ) ≤
          c₂ * Real.sqrt (((2 ^ n : ℕ) : ℝ) * Real.logb 2 (M : ℝ) /
            (Real.logb 2 (((2 ^ n : ℕ) : ℝ) / Real.logb 2 (M : ℝ)) + 1))) := by
  sorry


end QAlgorithms.LearningSurvey

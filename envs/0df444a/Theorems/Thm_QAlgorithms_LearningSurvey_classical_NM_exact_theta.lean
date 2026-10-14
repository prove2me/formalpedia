-- Prove2me | Theorems.Thm_QAlgorithms_LearningSurvey_classical_NM_exact_theta
-- name    : QAlgorithms.LearningSurvey.classical_NM_exact_theta
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:55:52.463212+00:00
-- url     : https://prove2.me/theorems/6d03c0d8-1abb-44f7-a00d-ab6115a295fc
-- title:
--   Classical (N,M)-query complexity of exact learning is Θ(min{M,N})
-- statement:
--   This is the folklore characterization of the classical $(N,M)$-query complexity of exact learning.
--
--   Let $N=2^n$ and let $M$ be an integer with $2\le M\le 2^N$. The classical $(N,M)$-query complexity $D(N,M)$ is the maximum, over all concept classes $C\subseteq\{0,1\}^N$ with $|C|=M$, of the classical membership query complexity of exactly learning $C$ (randomized learners, success probability at least $2/3$ on every target, worst-case number of queries). There are absolute constants $c_1,c_2>0$ such that for all such $n$ and $M$
--   $$c_1\min\{M,N\}\ \le\ D(N,M)\ \le\ c_2\min\{M,N\}.$$
--
--   It is the classical benchmark against which Kothari's quantum characterization (Theorem 4.6) is compared.
--
--   **Formalization Note** $N$ is restricted to powers of two, as throughout §4.1. The case $M=1$ is excluded: the only class has one concept and needs no queries, so the lower bound of the $\Theta$ is meant for $M\ge 2$. The bound $M\le 2^N$ excludes sizes for which no class exists.
-- source:
--   Srinivasan Arunachalam and Ronald de Wolf, A Survey of Quantum Learning Theory, 2017, v3, PDF p. 10, §4.1.2, Theorem 4.5. https://arxiv.org/pdf/1701.06806v3

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
set_option autoImplicit false

namespace QAlgorithms.LearningSurvey

universe u



/-- **Theorem 4.5** (folklore; survey p.10). The classical `(N, M)`-query complexity of exact
learning is `Θ(min{M, N})`, for `N = 2^n` and every class size `2 ≤ M ≤ 2^N`. -/
theorem classical_NM_exact_theta :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ (n M : ℕ), 2 ≤ M → M ≤ 2 ^ (2 ^ n) →
      c₁ * (min M (2 ^ n) : ℕ) ≤ (Learning.classicalExactNM n M : ℝ) ∧
        (Learning.classicalExactNM n M : ℝ) ≤ c₂ * (min M (2 ^ n) : ℕ) := by
  sorry



end QAlgorithms.LearningSurvey

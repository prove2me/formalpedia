-- Prove2me | Theorems.Thm_QAlgorithms_LearningSurvey_servedioGortler_classical_le_cube
-- name    : QAlgorithms.LearningSurvey.servedioGortler_classical_le_cube
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:55:12.520013+00:00
-- url     : https://prove2.me/theorems/20151c90-ce4b-4362-a25a-5c87a6ee4f99
-- title:
--   Servedio–Gortler: D(C) = O(n·Q(C)^3)
-- statement:
--   This corollary says that classical and quantum exact learning from membership queries are polynomially related.
--
--   Let $n\ge 1$, $N=2^n$, and let $C\subseteq\{0,1\}^N$ be a class of concepts $c:\{0,1\}^n\to\{0,1\}$. Let $D(C)$ be the classical membership query complexity of exactly learning $C$: the least $T$ such that some randomized classical learner, which queries $c(x)$ at most $T$ times on every target and for every outcome of its internal randomness, outputs $h=c$ with probability at least $2/3$ for every $c\in C$. Let $Q(C)$ be the quantum analogue, the least number of queries to $O_c:|x,b\rangle\mapsto|x,b\oplus c(x)\rangle$ of a quantum exact learner for $C$. Then there is an absolute constant $K>0$ such that
--   $$D(C)\ \le\ K\, n\, Q(C)^3 .$$
--
--   It shows that quantum membership queries can give at most a polynomial speed-up for exact learning.
--
--   **Formalization Note** $D(C)$ and $Q(C)$ are the infima of the (nonempty) sets of achievable query counts; for $Q(C)$ the workspace dimension ranges over all finite sizes.
-- source:
--   Srinivasan Arunachalam and Ronald de Wolf, A Survey of Quantum Learning Theory, 2017, v3, PDF p. 10, §4.1.1, Corollary 4.4. https://arxiv.org/pdf/1701.06806v3

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances
set_option autoImplicit false

namespace QAlgorithms.LearningSurvey

universe u


/-- **Corollary 4.4** (Servedio–Gortler; survey p.10). If a concept class `C ⊆ {0,1}^N`
(`N = 2^n`) has classical and quantum membership query complexities `D(C)` and `Q(C)`, then
`D(C) = O(n Q(C)^3)`. -/
theorem servedioGortler_classical_le_cube :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (C : Finset (Qubits n → Bool)),
      (Learning.classicalExactComplexity C : ℝ) ≤
        K * (n : ℝ) * (Learning.quantumExactComplexity C : ℝ) ^ 3 := by
  sorry




end QAlgorithms.LearningSurvey

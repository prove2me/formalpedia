-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_exactLearning_NM_lowerBound
-- name    : QAlgorithms.Arunachalam.exactLearning_NM_lowerBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:53:50.537634+00:00
-- url     : https://prove2.me/theorems/f78253d5-0c0b-4dd3-a6b6-46a885e7fd38
-- title:
--   A class of size at most M needing Ω(√((N−k+1)k)) quantum membership queries
-- statement:
--   This is the lower-bound lemma behind Kothari's characterization of the $(N,M)$-quantum query complexity of exact learning.
--
--   A concept is an $N$-bit string $c\in\{0,1\}^N$ (its truth table on $[N]$), and a concept class is a set $\mathcal C\subseteq\{0,1\}^N$. A quantum exact learner for $\mathcal C$ is a $T$-query algorithm $U_T O_c U_{T-1}\cdots O_c U_0$ acting on a fixed start state, with unitaries $U_0,\dots,U_T$ independent of $c$, a finite workspace, and the membership oracle $O_c:|x,b\rangle\mapsto|x,b\oplus c(x)\rangle$; it must output $c$ with probability at least $2/3$ for every $c\in\mathcal C$.
--
--   There is an absolute constant $c_0>0$ such that for all $N,M\in\mathbb N$ there exists $\mathcal C\subseteq\{0,1\}^N$ with $|\mathcal C|\le M$ such that, for every integer $k$ with $1\le k\le N$ and $\binom{N}{k-1}+\binom{N}{k}\le M$, every quantum exact learner for $\mathcal C$ making $T$ queries satisfies
--
--   $$
--   T\ \ge\ c_0\sqrt{(N-k+1)\,k}.
--   $$
--
--   Together with Fact 6.4.9 this gives the lower bound $\Omega\big(\sqrt{N\log M/(\log(N/\log M)+1)}\big)$ of Theorem 6.4.7 for $N<M\le 2^N$.
--
--   **Formalization Note** The learner is the frozen `QueryAlg` with the XOR oracle and an arbitrary finite workspace type; the Ω-constant is quantified before $N$ and $M$. The range $1\le k\le N$ is the one of the proof (Hamming weights $k-1$ and $k$).
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 133, Lemma 6.4.8. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_Learning
set_option autoImplicit false

namespace QAlgorithms.Arunachalam

open QAlgorithms.Learning

/-- Arunachalam p.133, Lemma 6.4.8: there is a concept class `C ⊆ {0,1}^N` with `|C| ≤ M` such
that every quantum exact learner for `C` (XOR membership oracle `QMQ(c)`, success probability
`≥ 2/3` on every `c ∈ C`, §6.3.1) makes `Ω(√((N − k + 1) k))` queries, for every `k ∈ [1, N]`
with `binom(N, k−1) + binom(N, k) ≤ M`. The constant of `Ω` is universal (chosen before `N`,
`M`); the learner may use any finite workspace (internal randomness via start state and
workspace). -/
theorem exactLearning_NM_lowerBound :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ N M : ℕ, ∃ C : Finset (Fin N → Bool), C.card ≤ M ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ N → N.choose (k - 1) + N.choose k ≤ M →
        ∀ (W : Type) [Fintype W] [DecidableEq W] (T : ℕ) (A : QueryAlg (Fin N) Bool W T)
          (out : (Fin N × Bool) × W → (Fin N → Bool)),
          IsQExactLearner A out C →
            c0 * Real.sqrt ((((N - k + 1 : ℕ) : ℝ)) * (k : ℝ)) ≤ (T : ℝ) := by
  sorry



end QAlgorithms.Arunachalam

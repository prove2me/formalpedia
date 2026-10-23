-- Prove2me | Theorems.Thm_TailOptCaching_ETLRU_lemma_1
-- name    : TailOptCaching.ETLRU.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:38.656325+00:00
-- url     : https://prove2.me/theorems/af5c53a0-6c6e-4101-8166-dd83aed70809
-- title:
--   Lemma 1, p. 19 — Policy 2 (greedy eviction by the smallest ranking criterion) returns an optimal solution to the ET-LRU problem (8)
-- statement:
--   Let $\xi$ be a natural number, let $s = (\lambda, L, X)$ be a well-formed belief state with $n$ arrived conversations, and let conversation $\theta \le n$ (existing, or new if $\theta = n$) arrive with prompt length $Q$ and response length $A$. **Policy 2** (Algorithm 2) first sets $L_\theta \leftarrow L_\theta + Q + A$, $X_\theta \leftarrow L_\theta$, $\lambda_\theta \leftarrow \bar\lambda_\theta$, and then performs
--   $$m = \Big(\sum_i X_i - C\Big)^+$$
--   eviction steps (with the updated $X$), each removing one cached token from a conversation $j$ with $X_j \ge 1$ that minimizes the ranking criterion
--   $$v_j = \lambda_j\, \mathbb P(L_j + Q_j - \xi \ge X_j),$$
--   recomputed after every eviction, ties broken arbitrarily. **Lemma 1:** the resulting cache vector is feasible for (9), (10) and the capacity constraint, and it minimizes the objective of (8),
--   $$\sum_i \lambda_i\, \mathbb E\big[(L_i + Q_i - Y_i - \xi)^+\big],$$
--   over all feasible $Y$.
--
--   Lemma 1 shows that ET-LRU can be implemented token by token with a min-heap, without solving (8) as an integer program.
--
--   **Formalization Note.** Algorithm 2 takes the number $n$ of tokens to evict as an input; here it is the number $m$ above (truncated subtraction in $\mathbb N$), the number that makes the output feasible. The hypothesis $\xi \in \mathbb N$ is added because the ranking criterion is the marginal cost only for integer $\xi$ (see the marginal-cost identity). The run of the algorithm is a relation, so the lemma holds for every tie-break.
-- source:
--   Zhang, Li, Moallemi & Peng, Tail-Optimized Caching for LLM Inference, arXiv:2510.15152v1, p. 19, Lemma 1; p. 20, Algorithm 2

import Mathlib
import Definitions.Def_TailOptCaching_ETLRU_Model

open scoped ENNReal

namespace TailOptCaching.ETLRU

theorem lemma_1 (P : Params) (hξ : ∃ m : ℕ, P.ξ = m) (s : State) (hs : WellFormed P s)
    (θ q a : ℕ) (hθ : θ ≤ s.n) (z : State)
    (hz : GreedyRun P
      ((∑ i ∈ Finset.range (nAfter s θ), Function.update s.X θ (s.L θ + q + a) i) - P.C)
      (post P s θ q a (Function.update s.X θ (s.L θ + q + a))) z) :
    Feasible P s θ q a z.X ∧
      ∀ Y, Feasible P s θ q a Y → nextTEL P z ≤ nextTEL P (post P s θ q a Y) := by sorry

end TailOptCaching.ETLRU

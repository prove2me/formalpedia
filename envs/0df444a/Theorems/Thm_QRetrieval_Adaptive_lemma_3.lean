-- Prove2me | Theorems.Thm_QRetrieval_Adaptive_lemma_3
-- name    : QRetrieval.Adaptive.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:52:52.951882+00:00
-- url     : https://prove2.me/theorems/0bfae298-d829-46ff-947e-995ef3b69179
-- title:
--   Lemma 3 — a bipartite graph $[k]\times[d]\to[2n]$ with $d=O(\max\{\log(k/n),1\})$ and $|\Gamma_G(A)|\ge|A|$ for $|A|\le n$
-- statement:
--   There is an absolute constant $C$ such that the following holds. For all natural numbers $n\ge1$ and $k$ there are a degree
--
--   $$
--   d\le C\cdot\max\{\log_2(k/n),\,1\}
--   $$
--
--   and a bipartite graph $G:[k]\times[d]\to[2n]$ such that every set $A\subseteq[k]$ of at most $n$ left vertices has at least $|A|$ neighbours:
--
--   $$
--   |\Gamma_G(A)|\ \ge\ |A|\qquad\text{for all }A\subseteq[k]\text{ with }|A|\le n .
--   $$
--
--   This expansion property is Hall's condition for sets of size at most $n$; through the remark that follows it, the graph lets any $n$ non-zero blocks of a string be routed injectively into $2n$ slots, which is the heart of the two-probe scheme of Lemma 6.
--
--   **Formalization Note** $[k],[d],[2n]$ are `Fin k`, `Fin d`, `Fin (2 * n)`, $G$ is curried, and $\Gamma_G(A)$ is `neighbors G A`. Real division is used inside the logarithm.
--
--   Differences from the source:
--   - encoding: d = O(max{log(k/n), 1}) (O(·), log of unspecified base) → ∃ C : ℝ chosen before every variable; log = Real.logb 2; reason: an absolute constant is what O(·) means here; the base of the logarithm only changes C
--   - encoding: for all n and k → 1 ≤ n; reason: log(k/n) is undefined at n = 0
--   - encoding: G : [k]×[d] → [2n], Γ_G(A) → G : Fin k → Fin d → Fin (2 * n), neighbors G A = ⋃_{a∈A} {G a j}; reason: 0-based indices and a curried map; same graphs
-- source:
--   Dhamapurkar, Garg, Paraashar, Radhakrishnan, Optimal compression with quantum retrieval, arXiv:2610.06702, Lemma 3, p. 5

import Mathlib
import Definitions.Def_QRetrieval_Adaptive_neighbors

namespace QRetrieval.Adaptive

/-- **Lemma 3 (bipartite expander with a matching condition).**
Dhamapurkar, Garg, Paraashar, Radhakrishnan, *Optimal compression with quantum retrieval*,
arXiv:2610.06702, Lemma 3, p. 5: "For all `n` and `k`, there is a bipartite graph
`G : [k]×[d] → [2n]` with `d = O(max{log(k/n), 1})` such that for every set `A ⊆ [k]` of size at
most `n`, we have `|Γ_G(A)| ≥ |A|`."

There is an absolute constant `C` such that for all `n ≥ 1` and all `k` there are `d ≤ C ·
max(log₂(k/n), 1)` and `G : Fin k → Fin d → Fin (2n)` with `|A| ≤ |Γ_G(A)|` for every
`A ⊆ Fin k` with `|A| ≤ n`.

**Formalization Note.** `O(·)` is an absolute constant `C` chosen before `n` and `k`;
`log = log₂` (the base only changes `C`). `n ≥ 1` because `log(k/n)` is undefined at `n = 0`.
Real division is used (`(k : ℝ) / n`); at `k = 0` Lean's `Real.logb 2 0 = 0`, and the `max` with
`1` makes the bound `C`, as in the paper. `[k]`, `[d]`, `[2n]` are `Fin k`, `Fin d`, `Fin (2n)`,
and `Γ_G(A)` is `neighbors G A`. -/
theorem lemma_3 : ∃ C : ℝ, ∀ n k : ℕ, 1 ≤ n →
    ∃ d : ℕ, (d : ℝ) ≤ C * max (Real.logb 2 ((k : ℝ) / n)) 1 ∧
      ∃ G : Fin k → Fin d → Fin (2 * n), ∀ A : Finset (Fin k), A.card ≤ n →
        A.card ≤ (neighbors G A).card := by sorry

end QRetrieval.Adaptive

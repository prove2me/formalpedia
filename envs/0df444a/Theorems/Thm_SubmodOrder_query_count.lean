-- Prove2me | Theorems.Thm_SubmodOrder_query_count
-- name    : SubmodOrder.query_count
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:38:45.42775+00:00
-- url     : https://prove2.me/theorems/72f43b43-36c4-4531-a1dd-791c12279d1b
-- title:
--   Proof of Theorem 2, p.20 — Threshold Add makes at most $n$ queries and Algorithm 1 at most $n(1+L)$ (corrected: $k=1$)
-- statement:
--   Let the ground set have $n$ elements, ordered by $\pi$, and let $f$ be any set function. Then:
--
--   1. for every cardinality $k$ and every threshold $\tau$, Threshold Add$(k,\tau)$ makes at most $n$ oracle queries;
--   2. for every $k$ and $\varepsilon$, Algorithm 1 makes at most
--   $$
--   n\,(1+L),\qquad L=\max\bigl(1,\lceil\log_{1+\varepsilon}k\rceil\bigr),
--   $$
--   oracle queries: $n$ for the singleton values that define $\tau$ and at most $n$ for each of its $L$ calls of Threshold Add.
--
--   For $\varepsilon\in(0,1)$ this gives the bound $O(\frac n\varepsilon\log k)$ of Theorem 2, since $\ln(1+\varepsilon)\ge\varepsilon/2$.
--
--   Differences from the source:
--   - correction: Algorithm 1 calls Threshold Add ⌈log_{1+ε} k⌉ times, "This results in O(n log_{1+ε} k)" queries → L = max(1, ⌈log_{1+ε} k⌉) calls and at most n(1 + L) queries, counting the n singleton queries for τ; reason: at k = 1 the printed count is 0, but the algorithm needs queries: for n = 2, k = 1 and f the indicator of containing a fixed element, a query-free program returns a fixed set and fails the guarantee for one of the two choices; the corrected Algorithm 1 makes 2 queries at n = k = 1
--   - generalization: ε ∈ (0,1), k ≥ 1, f monotone subadditive with a weak submodular order → every real ε, every k and every f : Finset α → ℝ; reason: the query count does not depend on these hypotheses; the statement specializes to the paper's
--   - encoding: "oracle queries" → OracleProg.queries along the run of the program against f; Threshold Add keeps f(S) and does not query f(∅) = 0; reason: the paper's "at most n queries" per Threshold Add counts one query per scanned element
--   - encoding: τ = 1/k max_{e∈N} f({e}); "Best of {S₁, …, S_L}" → τ = max(0, max_e f({e}))/k; the first set of largest value, compared by the values returned by Threshold Add; reason: equal to the paper for monotone f with f(∅) = 0 on a nonempty ground set; neither changes the number of queries, and the best-of comparison makes no query
-- source:
--   Udwani, Submodular Order Functions and Assortment Optimization, arXiv:2107.02743v5, proof of Theorem 2, §4.1, p.20

import Mathlib
import Definitions.Def_SubmodOrder_OracleProg
import Definitions.Def_SubmodOrder_thresholdAdd
import Definitions.Def_SubmodOrder_algorithm1

namespace SubmodOrder

/-- Query count of Algorithms 1 and 2 (Udwani, arXiv:2107.02743v5, proof of Theorem 2, §4.1,
p.20: "The Threshold Add subroutine makes at most n queries. Algorithm 1 calls the Threshold Add
subroutine ⌈log1+ε k⌉ times.").

For every set function `f`: Threshold Add(k, τ) makes at most `n` oracle queries, for every
threshold `τ`; and Algorithm 1 makes at most `n · (1 + L)` queries, `L = max(1, ⌈log_{1+ε} k⌉)`:
`n` queries for the singletons that define `τ`, and at most `n` for each of the `L` calls of
Threshold Add.

**Formalization Note.** Queries are counted by `OracleProg.queries` along the execution path
selected by the answers of `f`. The `n` singleton queries of the initialization
`τ = 1/k max_e f({e})` are counted; the printed count omits them, and the printed number of
calls `⌈log_{1+ε} k⌉` is `0` at `k = 1`, where the corrected Algorithm 1 still makes one call. -/
theorem query_count {α : Type*} [DecidableEq α] {n : ℕ} (π : α ≃ Fin n) (k : ℕ)
    (f : Finset α → ℝ) :
    (∀ τ : ℝ, OracleProg.queries f (thresholdAdd π k τ) ≤ n) ∧
      ∀ ε : ℝ, OracleProg.queries f (algorithm1 π k ε) ≤ n * (1 + numRounds k ε) := by sorry

end SubmodOrder

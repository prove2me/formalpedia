-- Prove2me | Theorems.Thm_TailOptCaching_ETLRU_Supplement_theorem_1
-- name    : TailOptCaching.ETLRU.Supplement.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T07:50:04.522682+00:00
-- url     : https://prove2.me/theorems/5d0cd40c-6703-4209-a2d9-0d873bf807b0
-- title:
--   Theorem 1, p. 6 (corrected: integer threshold ξ) — Tail-Optimized Belady (TEL-safe cap + furthest-in-future eviction) is hindsight optimal for TEL
-- statement:
--   Fix a deterministic trace with $N$ conversations, request-time sets $\mathcal T_i\subseteq[T]$ (pairwise disjoint) and turn lengths $q_{i,t},a_{i,t}$ in blocks, a cache capacity $C\in\mathbb N$ and an integer threshold $\xi\in\mathbb N$. Write
--   $$\mathrm{TEL}(x)=\sum_{i\in[N]}\sum_{t\in\mathcal T_i}\Bigl(\sum_{j=1}^{t}q_{i,j}+\sum_{j=1}^{t-1}a_{i,j}-x_{i,t}-\xi\Bigr)^+$$
--   for the Tail Excess Latency (divided by the TTFT slope $\alpha$) of a caching state $x$, and call $x$ feasible when it starts from the empty cache and satisfies the capacity, history and no-growth constraints (4)–(6).
--
--   **Tail-Optimized Belady** chooses the cache for $t+1$ by first capping every conversation $j$ at the TEL-safe budget $\bigl(\sum_{l\le s}q_{j,l}+\sum_{l<s}a_{j,l}-\xi\bigr)^+$ of its next request $s$ (and at $0$ if it never requests again), within what (5)–(6) allow, and then, if the capped total exceeds $C$, evicting blocks one at a time from a conversation whose next request is furthest in the future, with any tie-breaking. Then:
--
--   1. a run of Tail-Optimized Belady exists; and every run $x$
--   2. is feasible for (4)–(6);
--   3. stays within the TEL-safe budget: $x_{i,t}\le\bigl(\sum_{j\le t}q_{i,j}+\sum_{j<t}a_{i,j}-\xi\bigr)^+$ for every $i$ and $t\in\mathcal T_i$;
--   4. minimizes TEL: $\mathrm{TEL}(x)\le\mathrm{TEL}(x')$ for every feasible $x'$, i.e. it is an optimal solution of the hindsight problem (7).
--
--   This is the hindsight benchmark of the paper. With $\xi=0$ it is Belady's furthest-in-future rule for the total number of reused blocks; for $\xi>0$ the cap discards blocks whose reuse cannot reduce the excess latency. It motivates the online Tail-Optimized LRU policy of §4.
--
--   **Formalization Note** The model is `TailOptCaching.ETLRU.Supplement.Trace`. A run is a relation (`IsTOBRun`), so the theorem covers every tie-breaking; the eviction loop is encoded by its outcomes ($x_{\cdot,t+1}\le y$, total $\min(C,\sum y)$, and any conversation with a later next request than an evicted one is emptied), which a brute-force check confirms are exactly the loop's outcomes. "Expected to arrive furthest in the future" is, in hindsight, the actual next request time, with "never again" furthest.
--
--   Differences from the source:
--   - correction: threshold ξ = ξ_s/α ≥ 0 real → ξ ∈ ℕ; reason: with fractional ξ the claim is false (one conversation, requests at t = 1 with q = 1, a = 0 and t = 2 with q = 0, C = 5, ξ = 1/2: the policy caches nothing at t = 2 and has TEL 1, while caching the block gives 1/2; an exact search finds 152 failures in 885 half-integer instances and none in 3000 integer ones); the source measures every length in blocks and takes u ∈ ℕ in (7)
--   - reading: "the hindsight-optimal policy restricts … within the TEL-safe budget … evicts … furthest in the future" → the policy defined by these two rules is feasible, stays within the budget and minimizes TEL; reason: not every optimal solution stays within the budget (with slack capacity, caching everything is also optimal), so the theorem is read as optimality of the described policy, as on p. 7 ("Tail-Optimized Belady") and in Step two of App. A
--   - reading: x_{i,1} unconstrained → x_{i,1} = 0 (empty initial cache); reason: the prose of (5) bounds the cache by the history up to time t, which is empty before the first request
--   - reading: "next requests expected to arrive furthest in the future" → the actual next request time, ∞ for a conversation that never requests again (whose cap is 0); reason: the trace is deterministic and known in hindsight
--   - generalization: the source presupposes the policy → the theorem also asserts that a run exists; reason: an extra conclusion, which rules out a vacuous statement; it contains the source claim
--   - encoding: TEL = α Σ (·)⁺ → Σ (·)⁺; reason: the factor α > 0 changes no minimizer
-- source:
--   Zhang, Li, Moallemi & Peng, Tail-Optimized Caching for LLM Inference, arXiv:2510.15152v1, p. 6, Theorem 1; p. 7 (Tail-Optimized Belady); pp. 16–17, App. A, Proof of Theorem 1

import Mathlib
import Definitions.Def_TailOptCaching_ETLRU_Supplement_Trace

namespace TailOptCaching.ETLRU.Supplement

theorem theorem_1 {N : ℕ} (tr : Trace N) (C ξ : ℕ) :
    (∃ x, IsTOBRun tr C ξ x) ∧
    ∀ x, IsTOBRun tr C ξ x →
      Feasible tr C x ∧ WithinBudget tr ξ x ∧
        ∀ y, Feasible tr C y → tel tr ξ x ≤ tel tr ξ y := by sorry

end TailOptCaching.ETLRU.Supplement

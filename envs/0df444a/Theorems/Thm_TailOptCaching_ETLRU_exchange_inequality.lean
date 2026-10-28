-- Prove2me | Theorems.Thm_TailOptCaching_ETLRU_exchange_inequality
-- name    : TailOptCaching.ETLRU.exchange_inequality
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:25.693997+00:00
-- url     : https://prove2.me/theorems/e30f7b9c-fef2-4fb0-a1da-e91be255a27f
-- title:
--   App. B, pp. 18–19 — exchange step: evicting a token of strictly smaller ranking score is no worse for the optimal cost-to-go
-- statement:
--   Let $\xi$ be a natural number and let $z = (\lambda, L, X)$ be a post-decision state with $n$ arrived conversations. Let $i, j < n$ be two conversations with at least one cached token each, and write $z^{(i)}$, $z^{(j)}$ for the states obtained from $z$ by evicting one token of $i$, respectively of $j$; assume both are well formed, and that the cache of $z$ exceeds the capacity by exactly one token, $\sum_{l<n} X_l = C + 1$, so that one token must be evicted. If the ranking scores satisfy
--   $$\lambda_i\, \mathbb P(L_i + Q_i - \xi \ge X_i) < \lambda_j\, \mathbb P(L_j + Q_j - \xi \ge X_j),$$
--   then for every number $r$ of remaining arrivals the Bellman optimum satisfies
--   $$V^\star_r\big(z^{(i)}\big) \le V^\star_r\big(z^{(j)}\big).$$
--
--   This is the exchange argument of the proof of Theorem 2: in the paper's notation, $J_{k+1}(\tilde\lambda, \tilde L, X(1)) \le J_{k+1}(\tilde\lambda, \tilde L, X(k))$, where $X(1)$ evicts from the conversation of lowest score.
--
--   **Formalization Note.** The inequality between the scores is strict: with equal scores the two evictions can have different future costs (exact dynamic-programming checks found such pairs), and the paper's "ascending order" does not address ties. The hypothesis $\xi \in \mathbb N$ is added as for Lemma 1. Well-formedness of the two post-eviction states carries the invariant $0 < \lambda_l \le \bar\lambda_l$ that every reachable state satisfies. The capacity hypothesis $\sum_{l<n} X_l = C + 1$ is the page's setting (the exchange is made among the tokens that must be evicted to restore the capacity constraint); it cannot be dropped: with slack capacity the deficit of the evicted token is never pushed out, its future cost is (probability that its conversation returns within the horizon) × (its tail probability), which is not linear in the rate, and an exact computation (C = 5, ξ = 1, λ_conv = 1, rates 1 and 2 with λ̄ = λ, L = X = 1, Q_0 ≡ 1, P(Q_1 = 1) = 11/20, A ≡ 0, decay factor 1, two arrivals) gives $V^\star_2(z^{(0)}) = 17/40 > 319/800 = V^\star_2(z^{(1)})$ although the score of 0 is 1 < 11/10.
-- source:
--   Zhang, Li, Moallemi & Peng, Tail-Optimized Caching for LLM Inference, arXiv:2510.15152v1, pp. 18–19, App. B (exchange argument and its three cases)

import Mathlib
import Definitions.Def_TailOptCaching_ETLRU_Model

open scoped ENNReal

namespace TailOptCaching.ETLRU

theorem exchange_inequality (P : Params) (hξ : ∃ m : ℕ, P.ξ = m) (r : ℕ) (z : State)
    (i j : ℕ) (hi : i < z.n) (hj : j < z.n) (hXi : 1 ≤ z.X i) (hXj : 1 ≤ z.X j)
    (hwi : WellFormed P (evict z i)) (hwj : WellFormed P (evict z j))
    (hcap : ∑ l ∈ Finset.range z.n, z.X l = P.C + 1)
    (hscore : score P z i < score P z j) :
    optValue P r (evict z i) ≤ optValue P r (evict z j) := by sorry

end TailOptCaching.ETLRU

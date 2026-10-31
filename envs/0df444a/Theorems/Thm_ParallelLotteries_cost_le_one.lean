-- Prove2me | Theorems.Thm_ParallelLotteries_cost_le_one
-- name    : ParallelLotteries.cost_le_one
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:36:50.734072+00:00
-- url     : https://prove2.me/theorems/68bca09e-0372-4a9b-8e5f-2c837127638e
-- title:
--   Every strategy's allocation costs at most one: $\chi_i(s,p)\le t_ip_i$ and $C(\chi(s,p))\le1$
-- statement:
--   Let $k\ge1$, let $p\in[0,1]^n$ be win probabilities, and let $s=(t,\succ)\in S_k$ be a strategy with at most $k$ tickets. Then
--
--   1. $\chi_i(s,p)\le t_i\,p_i$ for every item $i$, and
--   2. the allocation $\chi(s,p)$ has cost at most one:
--   $$C(\chi(s,p))=\frac1k\sum_i\frac{\chi_i(s,p)}{p_i}\le\frac1k\sum_i t_i\le 1.$$
--
--   In particular, in a $k$-ticket equilibrium $(\Phi,p)$ every agent's allocation $x(v)=\chi(\Phi(v),p)$ satisfies $C(x(v))\le1$. This is the budget constraint that drives the proof of Theorem 2.
--
--   Differences from the source:
--   - reading: the page's final "$=1$" ($\frac1k\sum_i\Phi_i(v)=1$) → $\le1$; reason: $S_k$ is the set of strategies with at most $k$ tickets (p.5), so $\sum_i t_i\le k$; the equality holds when all $k$ tickets are used
--   - reading: $C(y)=\frac1k\sum_i y_i/p_i$ → the sum over items with $p_i>0$; reason: the page divides by $p_i$ without comment; when every $p_i>0$ this is (49) verbatim
--   - generalization: the statement for $x(v)=\chi(\Phi(v),p)$ at an equilibrium → for every strategy $s\in S_k$ and every $p\in[0,1]^n$; reason: the page's argument uses only $\chi_i\le t_ip_i$; taking $s=\Phi(v)$ gives the printed statement
-- source:
--   Arnosti–Randolph, Alaskan Hunting License Lotteries Are Flexible and Approximately Efficient, SSRN 3370605 (preprint), App. D.2, display after (49), p.32

import Mathlib
import Definitions.Def_ParallelLotteries_Model
import Definitions.Def_ParallelLotteries_Budget

namespace ParallelLotteries

/-- **Every strategy's allocation costs at most one** — Arnosti–Randolph, *Alaskan Hunting License
Lotteries Are Flexible and Approximately Efficient*, SSRN 3370605 (preprint), App. D.2, display
after (49), p.32: "Because χ_i(Φ(v), p) ≤ Φ_i(v) p_i, we have that under x, every agent receives
an allocation with cost at most one: C(x(v)) = 1/k ∑_i χ_i(Φ(v), p)/p_i ≤ 1/k ∑_i Φ_i(v) = 1."

For win probabilities `p ∈ [0, 1]ⁿ` and every strategy `s ∈ S_k`:
1. `χ_i(s, p) ≤ t_i p_i` for every item `i`;
2. `C(χ(s, p)) ≤ 1`, with `C` the cost (49).
Applied to `s = Φ(v)` this is the printed statement for `x(v) = χ(Φ(v), p)`.

**Formalization Note.** The printed final "= 1" uses `∑_i t_i = k`; strategies in `S_k` have at
most `k` tickets, so the conclusion is `≤ 1`. The cost sums over items with `p_i > 0` (see
`ParallelLotteries.cost`). -/
theorem cost_le_one {n k : ℕ} (hk : 1 ≤ k) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (s : Strategy n k) :
    (∀ i, chi s p i ≤ (s.tickets i : ℝ) * p i) ∧ cost k p (chi s p) ≤ 1 := by sorry

end ParallelLotteries

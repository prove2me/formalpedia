-- Prove2me | Theorems.Thm_ParallelLotteries_budget_lp_two_support
-- name    : ParallelLotteries.budget_lp_two_support
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:36:51.920146+00:00
-- url     : https://prove2.me/theorems/753425d6-345c-426f-887a-9f69fe38776f
-- title:
--   The budget problem (51) has an optimum with at most two nonzero entries
-- statement:
--   Let $k\ge1$, let $0<p_i\le1$ for every item $i$, and let $v\in\mathbb R^n$ be a type. Consider the budget problem (51)
--   $$\max\Bigl\{\,y\cdot v\;:\;y\in[0,1]^n,\ \sum_i y_i\le1,\ C(y)=\frac1k\sum_i\frac{y_i}{p_i}\le1\Bigr\}.$$
--   It has a maximizer $y$ with at most two nonzero entries.
--
--   The paper derives this from the fact that (51) is an agent's problem in a competitive equilibrium from equal incomes (CEEI) in which item $i$ has price $1/(kp_i)$ (Hylland and Zeckhauser 1979). It reduces the proof of Theorem 2 to a single-item case and a two-item case.
--
--   Differences from the source:
--   - reading: the feasible set $\{y: C(y)\le1\}$ of (51) → fractional allocations $y\in[0,1]^n$ with $\sum_iy_i\le1$ and $C(y)\le1$; reason: $y$ is "a fractional allocation" in (49); over all of $\mathbb R^n$ the maximum is unbounded
--   - reading: the tacit $p_i>0$ of (49) → the hypothesis $0<p_i\le1$ for every $i$; reason: (49) divides by $p_i$, and $p_i$ is a win probability
--   - reading: "every agent has an optimal strategy which purchases at most two items" → (51) has a maximizer with at most two nonzero entries; reason: this is the claim the proof uses ("select $y\in Y_v$ with the minimum number of nonzero entries"); the identification with a CEEI agent problem is the page's justification, not a separate claim
-- source:
--   Arnosti–Randolph, Alaskan Hunting License Lotteries Are Flexible and Approximately Efficient, SSRN 3370605 (preprint), App. D.2, (51) and the sentence after it, p.32

import Mathlib
import Definitions.Def_ParallelLotteries_Budget

namespace ParallelLotteries

/-- **The budget problem has an optimum on at most two items** — Arnosti–Randolph,
SSRN 3370605 (preprint), App. D.2, display (51), p.32: "For a given agent v, the set
Y_v := argmax_{y : C(y) ≤ 1} y · v (51) consists of the solutions to the agent decision problem in
an instance of CEEI in which each item i has an equilibrium price of 1/kp_i. As such, every agent
has an optimal strategy which purchases at most two items (Hylland and Zeckhauser (1979))."

For `k ≥ 1`, win probabilities `0 < p_i ≤ 1` and any type `v ∈ ℝⁿ`, the problem
`max { y · v : y ∈ [0, 1]ⁿ, ∑_i y_i ≤ 1, C(y) ≤ 1 }` has a maximizer `y` with at most two nonzero
entries.

**Formalization Note.** The feasible set of (51) is read as fractional allocations
(`y ∈ [0, 1]ⁿ`, `∑ y_i ≤ 1`), as in `ParallelLotteries.IsBudgetFeasible`. The conclusion contains
the existence of a maximizer. The hypothesis `p_i > 0` is the paper's tacit condition for dividing
by `p_i` in (49). The identification with a CEEI agent problem is commentary and is not stated. -/
theorem budget_lp_two_support {n k : ℕ} (hk : 1 ≤ k) (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i ≤ 1) (v : Fin n → ℝ) :
    ∃ y : Fin n → ℝ, IsBudgetOptimal k p v y ∧ (support y).card ≤ 2 := by sorry

end ParallelLotteries

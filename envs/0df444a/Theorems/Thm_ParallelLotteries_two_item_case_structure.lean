-- Prove2me | Theorems.Thm_ParallelLotteries_two_item_case_structure
-- name    : ParallelLotteries.two_item_case_structure
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:36:59.211535+00:00
-- url     : https://prove2.me/theorems/dcc88c91-b73b-45b6-a152-4c728b0509ed
-- title:
--   Two-item case: $p_i<1/k<p_j$ (53) and $y_i+y_j=1$ (54)
-- statement:
--   Let $k\ge1$, let $0<p_l\le1$ for every item $l$, and let $v$ be a type. Let $y$ solve the budget problem (51) with the minimum number of nonzero entries among all its solutions, and suppose its nonzero entries are exactly two items $i\neq j$ with $p_i\le p_j$. Then
--
--   1. the two win probabilities straddle $1/k$:
--   $$p_i<\frac1k<p_j; \tag{53}$$
--   2. without loss of generality $y_i+y_j=1$ (54): there is a solution $y'$ of (51) whose nonzero entries are exactly $i$ and $j$ and which satisfies
--   $$y'_i+y'_j=1.$$
--
--   So in the two-item case the agent's best affordable bundle combines a cheap item ($p_i<1/k$, price above $1$) with an expensive one ($p_j>1/k$, price below $1$) and fills the unit-demand constraint.
--
--   Differences from the source:
--   - reading: "Thus we can assume $y_i+y_j=1$ (54) without loss of generality" → there is a solution $y'$ of (51) with the same two nonzero entries and $y'_i+y'_j=1$; reason: a statement made without loss of generality is the existence of such a solution
--   - reading: the feasible set $\{y: C(y)\le1\}$ of (51) → fractional allocations $y\in[0,1]^n$ with $\sum_iy_i\le1$ and $C(y)\le1$; reason: $y$ is "a fractional allocation" in (49); over all of $\mathbb R^n$ the maximum is unbounded
--   - reading: the tacit $p_i>0$ of (49) → the hypothesis $0<p_l\le1$ for every $l$; reason: (49) divides by $p_l$, and $p_l$ is a win probability
-- source:
--   Arnosti–Randolph, Alaskan Hunting License Lotteries Are Flexible and Approximately Efficient, SSRN 3370605 (preprint), App. D.2, (53) and (54), p.33 (choice of $y$: p.32)

import Mathlib
import Definitions.Def_ParallelLotteries_Budget

namespace ParallelLotteries

/-- **The two-item case: (53) and (54)** — Arnosti–Randolph, SSRN 3370605 (preprint), App. D.2,
p.33: "Next, suppose that y has two nonzero components. Without loss of generality, suppose that
these components are y_i and y_j and that p_i ≤ p_j. First, we observe that p_i < 1/k < p_j. (53)
[…] Furthermore, if y_i + y_j < 1, we could weakly improve y · v by exchanging probability shares
to increase the share of argmax_{l∈{i,j}} p_l v_l until y_i + y_j = 1 (or until we reached an
allocation with a single item, which would contradict our choice of y.) Thus we can assume
y_i + y_j = 1 (54) without loss of generality."

Let `k ≥ 1`, `0 < p_l ≤ 1` for every item `l`, and `v ∈ ℝⁿ`. Let `y` be a maximizer of the budget
problem (51) with the minimum number of nonzero entries among all maximizers ("select y ∈ Y_v with
the minimum number of nonzero entries", p.32), and suppose its nonzero entries are exactly two
items `i ≠ j` with `p_i ≤ p_j`. Then
1. (53) `p_i < 1/k < p_j`;
2. (54) there is a maximizer `y′` of (51) whose nonzero entries are exactly `i` and `j` and
   which satisfies `y′_i + y′_j = 1`.

**Formalization Note.** "We can assume (54) without loss of generality" is stated as the
existence of such a maximizer `y′` (with the same support as `y`, hence also of minimum support).
`p_l > 0` is the paper's tacit condition for the cost (49). -/
theorem two_item_case_structure {n k : ℕ} (hk : 1 ≤ k) (p : Fin n → ℝ)
    (hp : ∀ l, 0 < p l ∧ p l ≤ 1) (v y : Fin n → ℝ) (hy : IsBudgetOptimal k p v y)
    (hmin : ∀ z, IsBudgetOptimal k p v z → (support y).card ≤ (support z).card)
    (i j : Fin n) (hij : i ≠ j) (hsupp : support y = {i, j}) (hpij : p i ≤ p j) :
    p i < 1 / (k : ℝ) ∧ 1 / (k : ℝ) < p j ∧
    ∃ y' : Fin n → ℝ, IsBudgetOptimal k p v y' ∧ support y' = {i, j} ∧ y' i + y' j = 1 := by sorry

end ParallelLotteries

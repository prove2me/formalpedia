-- Prove2me | Theorems.Thm_ParallelLotteries_single_item_ratio_bound
-- name    : ParallelLotteries.single_item_ratio_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:36:47.325577+00:00
-- url     : https://prove2.me/theorems/1e9901c8-1586-489d-aa3e-66f4e80fd858
-- title:
--   Single-item case (52): $\min(kp,1)/(1-(1-p)^k)\le1/(1-(1-1/k)^k)$
-- statement:
--   Let $k\ge1$. The single-item case of the proof of Theorem 2 rests on four facts.
--
--   1. For every $q\in(0,1]$,
--   $$\frac{\min(kq,1)}{1-(1-q)^k}\le\frac{1}{1-(1-1/k)^k},$$
--   i.e. the left-hand side is maximized at $q=1/k$.
--   2. Every budget-feasible $y$ (a fractional allocation with $C(y)\le1$) satisfies $y_j\le\min(kp_j,1)$ for every item $j$ with $p_j>0$.
--   3. If $\Phi$ is optimal given $p\in[0,1]^n$, then for every type $v$ and item $j$
--   $$x(v)\cdot v=w(v,\Phi(v),p)\ge\bigl(1-(1-p_j)^k\bigr)v_j,$$
--   since the chosen strategy is at least as good as putting all $k$ tickets on item $j$.
--   4. If moreover $p_j>0$ and $y$ is budget-feasible with $j$ as its only nonzero entry, then
--   $$y\cdot v\le\frac{\min(kp_j,1)}{1-(1-p_j)^k}\;x(v)\cdot v.$$
--
--   Together with $x'(v)\cdot v\le y\cdot v$ they give the chain (52): if the budget optimum $y$ has a single nonzero entry $y_j$, then
--   $$\frac{x'(v)\cdot v}{x(v)\cdot v}\le\frac{y\cdot v}{x(v)\cdot v}\le\frac{\min(kp_j,1)}{1-(1-p_j)^k}\le\frac{1}{1-(1-1/k)^k}.$$
--
--   Differences from the source:
--   - reading: the ratio chain (52) → its last two inequalities, the middle one multiplied through by $x(v)\cdot v$ (items 1 and 4), with the page's two ingredients (items 2 and 3); reason: the ratios are undefined when $x(v)\cdot v=0$; the first inequality $x'(v)\cdot v\le y\cdot v$ is the optimality of $y$ in (51), which the proof of Theorem 2 uses
--   - generalization: $y_j\le\min(kp_j,1)$ and $y\cdot v\le\frac{\min(kp_j,1)}{1-(1-p_j)^k}x(v)\cdot v$ for the budget optimum with the single nonzero entry $j$, and $x(v)\cdot v\ge(1-(1-p_j)^k)v_j$ for that $j$ → for every budget-feasible $y$ and every item $j$ with $p_j>0$, and for every type $v$ and every item $j$; reason: the page's arguments use only feasibility and optimality; the printed case is an instance
-- source:
--   Arnosti–Randolph, Alaskan Hunting License Lotteries Are Flexible and Approximately Efficient, SSRN 3370605 (preprint), App. D.2, (52) and the sentences before it, p.32

import Mathlib
import Definitions.Def_ParallelLotteries_Model
import Definitions.Def_ParallelLotteries_Budget

namespace ParallelLotteries

/-- **The single-item case** — Arnosti–Randolph, SSRN 3370605 (preprint), App. D.2, display (52),
p.32: "First, suppose that y_j > 0 for a single value j ∈ [n]. Then y_j ≤ min(kp_j, 1), and
y · v ≤ min(kp_j, 1)v_j. Meanwhile, x(v) · v ≥ (1 − (1 − p_j)^k)v_j, since the chosen strategy
must be at least as good as using all k tickets on item j. It follows that
x′(v)·v / x(v)·v ≤ y·v / x(v)·v ≤ min(kp_j, 1)/(1 − (1 − p_j)^k) ≤ 1/(1 − (1 − 1/k)^k), (52)
where the final inequality follows because the expression above is maximized at p_j = 1/k."

For every `k ≥ 1`:
1. (the final inequality of (52)) for every `q ∈ (0, 1]`,
   `min(kq, 1)/(1 − (1 − q)^k) ≤ 1/(1 − (1 − 1/k)^k)`;
2. every budget-feasible `y` (fractional allocation with `C(y) ≤ 1`) has `y_j ≤ min(k p_j, 1)`
   for every item `j` with `p_j > 0`;
3. if `Φ` is optimal given `p ∈ [0, 1]ⁿ`, then for every type `v` and item `j`,
   `w(v, Φ(v), p) = x(v) · v ≥ (1 − (1 − p_j)^k) v_j`;
4. (the middle inequality of (52), multiplied through by `x(v) · v`) if moreover `p_j > 0` and `y`
   is budget-feasible with `j` as its only nonzero entry, then
   `y · v ≤ (min(k p_j, 1)/(1 − (1 − p_j)^k)) · w(v, Φ(v), p)`.

**Formalization Note.** The ratios of (52) are written multiplicatively, since `x(v) · v` may be `0`.
Clauses 1 and 4 are the last two inequalities of (52); the first, `x′(v) · v ≤ y · v`, is the
optimality of `y` in (51) and is used in the proof of Theorem 2. -/
theorem single_item_ratio_bound (k : ℕ) (hk : 1 ≤ k) :
    (∀ q : ℝ, 0 < q → q ≤ 1 →
      min ((k : ℝ) * q) 1 / (1 - (1 - q) ^ k) ≤ 1 / (1 - (1 - 1 / (k : ℝ)) ^ k)) ∧
    (∀ {n : ℕ} (p : Fin n → ℝ) (y : Fin n → ℝ) (j : Fin n), 0 < p j →
      IsBudgetFeasible k p y → y j ≤ min ((k : ℝ) * p j) 1) ∧
    (∀ {n : ℕ} (p : Fin n → ℝ), (∀ i, 0 ≤ p i ∧ p i ≤ 1) →
      ∀ Φ : (Fin n → ℝ) → Strategy n k, IsOptimal p Φ →
        ∀ (v : Fin n → ℝ) (j : Fin n), (1 - (1 - p j) ^ k) * v j ≤ welfare v (Φ v) p) ∧
    (∀ {n : ℕ} (p : Fin n → ℝ), (∀ i, 0 ≤ p i ∧ p i ≤ 1) →
      ∀ Φ : (Fin n → ℝ) → Strategy n k, IsOptimal p Φ →
        ∀ (v y : Fin n → ℝ) (j : Fin n), 0 < p j → IsBudgetFeasible k p y → support y = {j} →
          ∑ i, y i * v i ≤
            min ((k : ℝ) * p j) 1 / (1 - (1 - p j) ^ k) * welfare v (Φ v) p) := by sorry

end ParallelLotteries

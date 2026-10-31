-- Prove2me | Theorems.Thm_ParallelLotteries_two_item_welfare_bound
-- name    : ParallelLotteries.two_item_welfare_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:36:56.178104+00:00
-- url     : https://prove2.me/theorems/da216b1d-4c0f-4ecb-9a45-b8b1e3fcffc5
-- title:
--   Two-item welfare bound (55)–(57): $y\cdot v\le\gamma\,x(v)\cdot v$ with $\gamma=\sum y_l/(1-(1-p_l)^k)$
-- statement:
--   Let $k\ge1$, let $p\in[0,1]^n$, let $\Phi$ be optimal given $p$, and write $x(v)\cdot v=w(v,\Phi(v),p)$ for the welfare of type $v$. For any two items $i,j$:
--
--   1. the agent prefers $x(v)$ to randomizing between all $k$ tickets on $i$ and all $k$ tickets on $j$: for every $\alpha\in[0,1]$,
--   $$x(v)\cdot v\ge\alpha\bigl(1-(1-p_i)^k\bigr)v_i+(1-\alpha)\bigl(1-(1-p_j)^k\bigr)v_j; \tag{55}$$
--   2. if $p_i,p_j>0$ and $y_i,y_j\ge0$ are not both zero, then with
--   $$\gamma=\frac{y_i}{1-(1-p_i)^k}+\frac{y_j}{1-(1-p_j)^k} \tag{58}$$
--   one has
--   $$y_iv_i+y_jv_j\le\gamma\;x(v)\cdot v,$$
--   which is (55) at the $\alpha$ of (56) that makes the randomized allocation the scaled copy $y/\gamma$ of $y$.
--
--   With $x'(v)\cdot v\le y\cdot v$ this gives (57), $x'(v)\cdot v/x(v)\cdot v\le\gamma$, in the two-item case of the proof of Theorem 2.
--
--   Differences from the source:
--   - reading: (56) defines $\alpha$ through $\alpha(1-(1-p_i)^k)/y_i=(1-\alpha)(1-(1-p_j)^k)/y_j=1/\gamma$ and (57) bounds a ratio → the multiplicative bound $y_iv_i+y_jv_j\le\gamma\,x(v)\cdot v$ with $\gamma$ given by (58), for $y_i,y_j\ge0$ not both zero; reason: (56) divides by $y_i,y_j$ and (57) by $x(v)\cdot v$; the step $x'(v)\cdot v\le y\cdot v$ of (57) is the optimality of $y$ in (51), used in the proof of Theorem 2
--   - generalization: $y$ a two-item solution of (51) with (53)–(54) → any two items $i,j$ with $p_i,p_j>0$ and any $y_i,y_j\ge0$ not both zero; reason: the page's argument uses only the optimality of $\Phi$; the printed case is an instance
-- source:
--   Arnosti–Randolph, Alaskan Hunting License Lotteries Are Flexible and Approximately Efficient, SSRN 3370605 (preprint), App. D.2, (55)–(56), p.33, and (57)–(58), p.34

import Mathlib
import Definitions.Def_ParallelLotteries_Model

namespace ParallelLotteries

/-- **Welfare lower bound in the two-item case: (55)–(57)** — Arnosti–Randolph, SSRN 3370605
(preprint), App. D.2, pp.33–34: "The agent must prefer x(v) to randomizing between using all
tickets on item i and using all tickets on item j. Therefore, for any α ∈ [0, 1] we have
x(v) · v ≥ α(1 − (1 − p_i)^k)v_i + (1 − α)(1 − (1 − p_j)^k)v_j. (55) We can set α so that the
allocation of this strategy is a scaled-down version of y:
α(1 − (1 − p_i)^k)/y_i = (1 − α)(1 − (1 − p_j)^k)/y_j ≜ 1/γ. (56) It follows from the fact that
x′(v) · v ≤ y · v and (55), (56) that x′(v)·v / x(v)·v ≤ y · v / ((1/γ) y · v) = γ. (57) […] Using (54)
and solving (56) for α, we can solve for γ: γ = y_i/(1 − (1 − p_i)^k) + y_j/(1 − (1 − p_j)^k) (58)".

Let `k ≥ 1`, `p ∈ [0, 1]ⁿ`, `Φ` optimal given `p`, `v` a type and `i, j` items. Then
1. (55) for every `α ∈ [0, 1]`,
   `w(v, Φ(v), p) ≥ α(1 − (1 − p_i)^k) v_i + (1 − α)(1 − (1 − p_j)^k) v_j`;
2. (56)–(58) if `p_i, p_j > 0` and `y_i, y_j ≥ 0` are not both zero, then with
   `γ = y_i/(1 − (1 − p_i)^k) + y_j/(1 − (1 − p_j)^k)`,
   `y_i v_i + y_j v_j ≤ γ · w(v, Φ(v), p)`, i.e. `x(v) · v ≥ (y · v)/γ` for `y` supported on
   `{i, j}`.

**Formalization Note.** `w(v, Φ(v), p) = x(v) · v` for the equilibrium allocation
`x(v) = χ(Φ(v), p)`. The step `x′(v) · v ≤ y · v` of (57) is the optimality of `y` in (51) and is
used in the proof of Theorem 2; it is not restated here. -/
theorem two_item_welfare_bound {n k : ℕ} (hk : 1 ≤ k) (p : Fin n → ℝ)
    (hp : ∀ l, 0 ≤ p l ∧ p l ≤ 1) (Φ : (Fin n → ℝ) → Strategy n k) (hΦ : IsOptimal p Φ)
    (v : Fin n → ℝ) (i j : Fin n) :
    (∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      α * (1 - (1 - p i) ^ k) * v i + (1 - α) * (1 - (1 - p j) ^ k) * v j ≤
        welfare v (Φ v) p) ∧
    (∀ yi yj : ℝ, 0 < p i → 0 < p j → 0 ≤ yi → 0 ≤ yj → 0 < yi + yj →
      yi * v i + yj * v j ≤
        (yi / (1 - (1 - p i) ^ k) + yj / (1 - (1 - p j) ^ k)) * welfare v (Φ v) p) := by sorry

end ParallelLotteries

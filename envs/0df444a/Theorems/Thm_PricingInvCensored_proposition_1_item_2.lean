-- Prove2me | Theorems.Thm_PricingInvCensored_proposition_1_item_2
-- name    : PricingInvCensored.proposition_1_item_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:51:15.172356+00:00
-- url     : https://prove2.me/theorems/39269348-9067-4df1-9cfa-c3f76e993765
-- title:
--   Proposition 1, Item 2: $y^*(p)=\lambda(p)+z_p$ with $F_\mu(z_p)=\phi(p)=\frac{b+p}{b+p+h}$
-- statement:
--   Assume Assumption 1 and let $p\in[\underline p,\overline p]$. There is a unique $z_p\in\mathbb R$ with
--   $$F_\mu(z_p)=\int_{-\infty}^{z_p}f_\mu(t)\,dt=\frac{b+p}{b+p+h}=:\phi(p),$$
--   and $y^*(p)=\lambda(p)+z_p$ is the unique maximizer of $y\mapsto Q(p,y)$ over $\mathbb R$.
--
--   This is the critical-fractile form of the optimal order-up-to level at a fixed price; the difference estimator of Algorithm 2 is built on it.
--
--   Differences from the source:
--   - reading: $y^*(p):=\arg\max_y Q(p,y)$ (p. 6; pp. 14 and 17 write $\arg\max_{y\in[0,\bar y]}$) → the maximizer over all real $y$; reason: p. 6 defines the arg max over $y$ without a range, and the $[0,\bar y]$ reading makes Item 2 false whenever $\lambda(p)+z_p>\bar y$.
--   - reading: "$z_p$ satisfies $F_\mu(z_p)=\phi(p)$" and "the arg max" → a unique such $z_p$ and a unique maximizer; reason: the paper uses $z_p$ and $y^*(p)$ as well-defined objects; uniqueness is the stronger reading.
--   - encoding: costs $b,h$ and the bound $|f_\mu'(u)|\le K$ of Assumption 1 → $b\ge0$, $h>0$, and $f_\mu$ differentiable at every $u$ of the band; reason: $b,h$ are per-unit penalty and holding costs (p. 5), $h>0$ is forced by Assumption 1(3) with compact support, and a bound on $f_\mu'(u)$ presupposes the derivative.
-- source:
--   Chen, Wang & Zhou, Optimal Policies for Dynamic Pricing and Inventory Control with Nonparametric Censored Demands, SSRN 3750413 (2022-10-19), Proposition 1 Item 2, p.11 (and the definition of y*(p), p.6)

import Mathlib
import Definitions.Def_PricingInvCensored_Model

open MeasureTheory Set

namespace PricingInvCensored

/-- **Proposition 1, Item 2**, Chen, Wang & Zhou, SSRN 3750413 (2022-10-19), p.11. Under
Assumption 1, for every `p ∈ [p̲, p̄]` there is a unique `z_p` with
`F_µ(z_p) = ∫_{−∞}^{z_p} f_µ(t) dt = (b + p)/(b + p + h) =: φ(p)`, and `y*(p) = λ(p) + z_p` is the
unique maximizer of `Q(p, ·)` over `ℝ`.

**Formalization Note.** `y*(p) := arg max_y Q(p, y)` is over all real `y` (p.6). The paper writes
"`z_p` satisfies" and "the arg max" as if unique; both uniqueness clauses are stated. -/
theorem proposition_1_item_2 (I : Instance) (pStar yStar : ℝ)
    (hA : Assumption1 I pStar yStar) (p : ℝ) (hp : p ∈ Icc I.market.low I.market.high) :
    ∃ z : ℝ, I.market.cdf z = (∫ t in Iic z, I.f t) ∧
      I.market.cdf z = I.market.quantileLevel p ∧
      (∀ z' : ℝ, I.market.cdf z' = I.market.quantileLevel p → z' = z) ∧
      (∀ y : ℝ, I.market.Q p y ≤ I.market.Q p (I.market.demand p + z)) ∧
      (∀ y : ℝ, (∀ y' : ℝ, I.market.Q p y' ≤ I.market.Q p y) → y = I.market.demand p + z) := by sorry

end PricingInvCensored

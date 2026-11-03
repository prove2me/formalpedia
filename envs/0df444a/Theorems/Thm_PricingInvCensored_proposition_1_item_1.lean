-- Prove2me | Theorems.Thm_PricingInvCensored_proposition_1_item_1
-- name    : PricingInvCensored.proposition_1_item_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:51:32.395402+00:00
-- url     : https://prove2.me/theorems/13aff093-11a2-48eb-a1b9-fd253779994e
-- title:
--   Proposition 1, Item 1 (corrected: second derivative at continuity points of $f_\mu$): $Q(p,\cdot)$ is concave with $\partial Q/\partial y=b+p-(b+p+h)F_\mu(y-\lambda(p))$
-- statement:
--   Assume Assumption 1 and let $p\in[\underline p,\overline p]$. Then $y\mapsto Q(p,y)$ is concave on $\mathbb R$ and continuously differentiable, with
--   $$\frac{\partial Q}{\partial y}(p,y)=b+p-(b+p+h)F_\mu(y-\lambda(p))\qquad\text{for all }y\in\mathbb R.$$
--   Moreover, at every $y$ such that the density $f_\mu$ is continuous at $y-\lambda(p)$,
--   $$\frac{\partial^2 Q}{\partial y^2}(p,y)=-(b+p+h)f_\mu(y-\lambda(p))\le 0 .$$
--
--   The first derivative is the stock-out signal that the bisection search of Algorithm 1 estimates; its sign change locates the optimal order-up-to level.
--
--   Differences from the source:
--   - correction: $\partial^2Q/\partial y^2=-(b+p+h)f_\mu(y-\lambda(p))$ for all $y\in[0,\bar y]$ → the second-derivative identity at every $y$ where $f_\mu$ is continuous at $y-\lambda(p)$; reason: false where $f_\mu$ jumps: with $b=h=1$, $[\underline p,\overline p]=[1/4,1]$, $\lambda(p)=3-2p$, $\mu=\mathrm{Uniform}[-1/2,1/2]$, $\bar y=3$, $p=1$, $y=3/2$, the derivative $\partial Q/\partial y$ has left derivative $-3$ and right derivative $0$, and every hypothesis holds.
--   - generalization: concavity, the first derivative and the sign for $y\in[0,\bar y]$ → for all $y\in\mathbb R$; reason: the formulas do not use the range, and the source's statement is the restriction to $[0,\bar y]$.
--   - encoding: costs $b,h$ and the bound $|f_\mu'(u)|\le K$ of Assumption 1 → $b\ge0$, $h>0$, and $f_\mu$ differentiable at every $u$ of the band; reason: $b,h$ are per-unit penalty and holding costs (p. 5), $h>0$ is forced by Assumption 1(3) with compact support, and a bound on $f_\mu'(u)$ presupposes the derivative.
-- source:
--   Chen, Wang & Zhou, Optimal Policies for Dynamic Pricing and Inventory Control with Nonparametric Censored Demands, SSRN 3750413 (2022-10-19), Proposition 1 Item 1, p.11

import Mathlib
import Definitions.Def_PricingInvCensored_Model

open MeasureTheory Set

namespace PricingInvCensored

/-- **Proposition 1, Item 1** (corrected), Chen, Wang & Zhou, SSRN 3750413 (2022-10-19), p.11.
Under Assumption 1, for every `p ∈ [p̲, p̄]`, `Q(p, ·)` is concave and continuously differentiable on
`ℝ` with `∂Q/∂y = b + p − (b + p + h)F_µ(y − λ(p))`, and at every `y` where `f_µ` is continuous at
`y − λ(p)` the second derivative is `∂²Q/∂y² = −(b + p + h)f_µ(y − λ(p)) ≤ 0`.

**Formalization Note.** Correction: the printed second-derivative clause for all `y ∈ [0, ȳ]` fails
where `f_µ` jumps (uniform noise at the edge of its support); it is stated at the continuity points
of the fixed density `f_µ`. The other clauses hold for all real `y`. -/
theorem proposition_1_item_1 (I : Instance) (pStar yStar : ℝ)
    (hA : Assumption1 I pStar yStar) (p : ℝ) (hp : p ∈ Icc I.market.low I.market.high) :
    ConcaveOn ℝ univ (I.market.Q p) ∧
      (∀ y : ℝ, HasDerivAt (I.market.Q p)
        (I.market.b + p - (I.market.b + p + I.market.h) * I.market.cdf (y - I.market.demand p))
        y) ∧
      Continuous (fun y : ℝ =>
        I.market.b + p - (I.market.b + p + I.market.h) * I.market.cdf (y - I.market.demand p)) ∧
      (∀ y : ℝ, ContinuousAt I.f (y - I.market.demand p) →
        HasDerivAt (fun y' : ℝ =>
            I.market.b + p - (I.market.b + p + I.market.h) * I.market.cdf (y' - I.market.demand p))
          (-(I.market.b + p + I.market.h) * I.f (y - I.market.demand p)) y) ∧
      (∀ y : ℝ, -(I.market.b + p + I.market.h) * I.f (y - I.market.demand p) ≤ 0) := by sorry

end PricingInvCensored

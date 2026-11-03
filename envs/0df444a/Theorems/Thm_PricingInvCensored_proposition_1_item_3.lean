-- Prove2me | Theorems.Thm_PricingInvCensored_proposition_1_item_3
-- name    : PricingInvCensored.proposition_1_item_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:51:24.922445+00:00
-- url     : https://prove2.me/theorems/2ad98285-d34e-492b-bb4e-af7e2773753b
-- title:
--   Proposition 1, Item 3: $G(p)=p\mathbb E[\min\{\lambda(p)+\varepsilon,y^*(p)\}]-b\mathbb E[(\varepsilon-z_p)^+]-h\mathbb E[(z_p-\varepsilon)^+]$
-- statement:
--   Assume Assumption 1, let $p\in[\underline p,\overline p]$, and let $z_p$ satisfy $F_\mu(z_p)=\phi(p)=\frac{b+p}{b+p+h}$, so that $y^*(p)=\lambda(p)+z_p$. Then
--   $$G(p)=p\,\mathbb E\big[\min\{\lambda(p)+\varepsilon,\,y^*(p)\}\big]-b\,\mathbb E\big[(\varepsilon-z_p)^+\big]-h\,\mathbb E\big[(z_p-\varepsilon)^+\big],$$
--   where $\varepsilon\sim\mu$ and $G(p)=\max_yQ(p,y)$.
--
--   This closed form is the starting point of the reward-difference decomposition, Eqs. (6)–(8).
--
--   Differences from the source:
--   - reading: $G(p)=\max_yQ(p,y)$ with $y^*(p)$ as in Item 2 → $G(p)=\sup_{y\in\mathbb R}Q(p,y)$ and $y^*(p)$ written as $\lambda(p)+z_p$ for any $z_p$ with $F_\mu(z_p)=\phi(p)$; reason: p. 6 maximizes over all real $y$, and $z_p$ is unique (Item 2).
--   - encoding: costs $b,h$ and the bound $|f_\mu'(u)|\le K$ of Assumption 1 → $b\ge0$, $h>0$, and $f_\mu$ differentiable at every $u$ of the band; reason: $b,h$ are per-unit penalty and holding costs (p. 5), $h>0$ is forced by Assumption 1(3) with compact support, and a bound on $f_\mu'(u)$ presupposes the derivative.
-- source:
--   Chen, Wang & Zhou, Optimal Policies for Dynamic Pricing and Inventory Control with Nonparametric Censored Demands, SSRN 3750413 (2022-10-19), Proposition 1 Item 3, p.11

import Mathlib
import Definitions.Def_PricingInvCensored_Model

open MeasureTheory Set

namespace PricingInvCensored

/-- **Proposition 1, Item 3**, Chen, Wang & Zhou, SSRN 3750413 (2022-10-19), p.11. Under
Assumption 1, for every `p ∈ [p̲, p̄]` and `z_p` with `F_µ(z_p) = φ(p)`,
`G(p) = p E[min{λ(p) + ε, y*(p)}] − b E[(ε − z_p)⁺] − h E[(z_p − ε)⁺]` with `y*(p) = λ(p) + z_p`.

**Formalization Note.** `G(p) = sup_{y ∈ ℝ} Q(p, y)`; `y*(p)` is written out as `λ(p) + z_p`
(Item 2). Expectations are Bochner integrals against `µ`. -/
theorem proposition_1_item_3 (I : Instance) (pStar yStar : ℝ)
    (hA : Assumption1 I pStar yStar) (p : ℝ) (hp : p ∈ Icc I.market.low I.market.high)
    (z : ℝ) (hz : I.market.cdf z = I.market.quantileLevel p) :
    G I p = p * (∫ ε, min (I.market.demand p + ε) (I.market.demand p + z) ∂I.market.noise)
      - I.market.b * (∫ ε, max (ε - z) 0 ∂I.market.noise)
      - I.market.h * (∫ ε, max (z - ε) 0 ∂I.market.noise) := by sorry

end PricingInvCensored

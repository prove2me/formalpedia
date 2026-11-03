-- Prove2me | Theorems.Thm_PricingInvCensored_eq_8
-- name    : PricingInvCensored.eq_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:51:27.5605+00:00
-- url     : https://prove2.me/theorems/84fc4076-7fad-4217-bc9c-bc0bdf5e8ac0
-- title:
--   Eq. (8): $1-\phi(p)=\frac{h}{b+p+h}=\Pr[\varepsilon\ge z_p]=\Pr[(z_{p'}-\varepsilon)^+\le z_{p'}-z_p]$
-- statement:
--   Assume Assumption 1, let $p<p'$ be prices in $[\underline p,\overline p]$, and let $z_p,z_{p'}$ satisfy $F_\mu(z_p)=\phi(p)$ and $F_\mu(z_{p'})=\phi(p')$, where $\phi(p)=\frac{b+p}{b+p+h}$. Then $z_p<z_{p'}$ and, for $\varepsilon\sim\mu$,
--   $$1-\phi(p)=\frac{h}{b+p+h}=\Pr[\varepsilon\ge z_p]=\Pr\big[(z_{p'}-\varepsilon)^+\le z_{p'}-z_p\big].$$
--
--   The last probability involves only the leftover stock $(z_{p'}-\varepsilon)^+$ at the level $y^*(p')$, which is observable under censoring; inverting its empirical distribution at level $\frac{h}{b+p+h}$ estimates $z_{p'}-z_p$ (Algorithm 2).
--
--   Differences from the source:
--   - reading: "(∗) holds because $z_{p'}>z_p$", with $z_p<z_{p'}$ stated on p. 15 → $z_p<z_{p'}$ is a conclusion of the theorem; reason: it is the page's justification of (∗), stated so that the item carries it.
--   - encoding: costs $b,h$ and the bound $|f_\mu'(u)|\le K$ of Assumption 1 → $b\ge0$, $h>0$, and $f_\mu$ differentiable at every $u$ of the band; reason: $b,h$ are per-unit penalty and holding costs (p. 5), $h>0$ is forced by Assumption 1(3) with compact support, and a bound on $f_\mu'(u)$ presupposes the derivative.
-- source:
--   Chen, Wang & Zhou, Optimal Policies for Dynamic Pricing and Inventory Control with Nonparametric Censored Demands, SSRN 3750413 (2022-10-19), Eq. (8), p.16 (with "Since p < p′, we have zp < zp′", p.15)

import Mathlib
import Definitions.Def_PricingInvCensored_Model

open MeasureTheory Set

namespace PricingInvCensored

/-- **Eq. (8)**, Chen, Wang & Zhou, SSRN 3750413 (2022-10-19), p.16 (with p.15). Under
Assumption 1, for prices `p < p′` in `[p̲, p̄]` and `z_p`, `z_{p′}` with `F_µ(z_p) = φ(p)`,
`F_µ(z_{p′}) = φ(p′)`: `z_p < z_{p′}` and
`1 − φ(p) = h/(b + p + h) = Pr[ε ≥ z_p] = Pr[(z_{p′} − ε)⁺ ≤ z_{p′} − z_p]`.

**Formalization Note.** Probabilities are `µ`-measures of the events, as real numbers. -/
theorem eq_8 (I : Instance) (pStar yStar : ℝ) (hA : Assumption1 I pStar yStar) (p p' : ℝ)
    (hp : p ∈ Icc I.market.low I.market.high) (hp' : p' ∈ Icc I.market.low I.market.high)
    (hpp' : p < p') (z z' : ℝ) (hz : I.market.cdf z = I.market.quantileLevel p)
    (hz' : I.market.cdf z' = I.market.quantileLevel p') :
    z < z' ∧
      1 - I.market.quantileLevel p = I.market.h / (I.market.b + p + I.market.h) ∧
      I.market.h / (I.market.b + p + I.market.h) = (I.market.noise (Ici z)).toReal ∧
      (I.market.noise (Ici z)).toReal =
        (I.market.noise {ε : ℝ | max (z' - ε) 0 ≤ z' - z}).toReal := by sorry

end PricingInvCensored

-- Prove2me | Theorems.Thm_PricingInvCensored_eq_EC17_first_term
-- name    : PricingInvCensored.eq_EC17_first_term
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:51:16.820823+00:00
-- url     : https://prove2.me/theorems/65d84093-a786-4450-8079-ff872e6b0d8f
-- title:
--   Eq. (EC.17), first term: $G(p^*)-G(p)\le S^2(U-L)^2$ for $p,p^*\in[L,U]$
-- statement:
--   Assume Assumptions 1 and 2, with clairvoyant price $p^*$. If $\underline p\le L\le U\le\overline p$ and both $p$ and $p^*$ lie in $[L,U]$, then
--   $$G(p^*)-G(p)\le S^2(U-L)^2 .$$
--
--   In the proof of Theorem 1 this bounds the price-suboptimality regret of epoch $\zeta$, $N_\zeta(G(p^*)-G(p_\zeta))\le N_\zeta S^2(U_\zeta-L_\zeta)^2$ for $p_\zeta\in\{\alpha_\zeta,\beta_\zeta\}$, using (EC.16).
--
--   Differences from the source:
--   - generalization: $N_\zeta(G(p^*)-G(p_\zeta))\le N_\zeta S^2(U_\zeta-L_\zeta)^2$ for $p_\zeta\in\{\alpha_\zeta,\beta_\zeta\}$ and the interval of Algorithm 3 → the per-period bound for any interval $[L,U]\subseteq[\underline p,\overline p]$ containing $p$ and $p^*$; reason: dividing by $N_\zeta>0$ gives the per-period form, and the source's case is $[L,U]=[L_\zeta,U_\zeta]$, $p=p_\zeta$.
--   - encoding: costs $b,h$ and the bound $|f_\mu'(u)|\le K$ of Assumption 1, and $s^2$ of Assumption 2 → $b\ge0$, $h>0$, $f_\mu$ differentiable at every $u$ of the band, and $s^2$ with $s>0$; reason: $b,h$ are per-unit penalty and holding costs (p. 5), $h>0$ is forced by Assumption 1(3) with compact support, a bound on $f_\mu'(u)$ presupposes the derivative, and only $s^2$ enters.
-- source:
--   Chen, Wang & Zhou, Optimal Policies for Dynamic Pricing and Inventory Control with Nonparametric Censored Demands, SSRN 3750413 (2022-10-19), Proof of Theorem 1, Step II, Eq. (EC.17) first term, p.ec8

import Mathlib
import Definitions.Def_PricingInvCensored_Model

open Set

namespace PricingInvCensored

/-- **Eq. (EC.17), first term**, Chen, Wang & Zhou, SSRN 3750413 (2022-10-19), p.ec8. Under
Assumptions 1 and 2, if the active interval `[L, U] ⊆ [p̲, p̄]` contains both `p*` and a price
`p`, then `G(p*) − G(p) ≤ S²(U − L)²`.

**Formalization Note.** The paper bounds `N_ζ(G(p*) − G(p_ζ))` by `N_ζ S²(U_ζ − L_ζ)²` for
`p_ζ ∈ {α_ζ, β_ζ}`; this is the per-period bound for every price of the interval. -/
theorem eq_EC17_first_term (I : Instance) (pStar yStar : ℝ) (hA1 : Assumption1 I pStar yStar)
    (hA2 : Assumption2 I) (L U p : ℝ) (hL : I.market.low ≤ L) (hU : U ≤ I.market.high)
    (hp : p ∈ Icc L U) (hpStar : pStar ∈ Icc L U) :
    G I pStar - G I p ≤ I.S ^ 2 * (U - L) ^ 2 := by sorry

end PricingInvCensored

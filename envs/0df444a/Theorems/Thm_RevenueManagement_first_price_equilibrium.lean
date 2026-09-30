-- Prove2me | Theorems.Thm_RevenueManagement_first_price_equilibrium
-- name    : RevenueManagement.first_price_equilibrium
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:52:29.541296+00:00
-- url     : https://prove2.me/theorems/0e8aac2e-117d-4567-820f-31c986497144
-- title:
--   Eq. (6.4): the bid b*(v) = v − ∫₀ᵛ P(s) ds / P(v) solves (6.3), is a symmetric equilibrium of the single-unit first-price auction, and shades below the valuation
-- statement:
--   For $N \ge 2$ customers with regular i.i.d. valuations, let $P(v) = F(v)^{N-1}$ and
--   $b^*(v) = v - \int_0^v P(s)\,ds / P(v)$. Then (a) on $(0, \bar v]$, $b^*$ satisfies the
--   first-order condition (6.3), $b^{*\prime}(v) = \frac{P'(v)}{P(v)}(v - b^*(v))$ with
--   $P'(v) = (N-1)F(v)^{N-2} f(v)$; (b) it is a symmetric equilibrium: a customer with valuation
--   $v$ bidding as a customer with valuation $w$ gets expected surplus
--   $P(w)(v - b^*(w)) \le P(v)(v - b^*(v))$; (c) $b^*(v) < v$ for $v > 0$, customers shade
--   their bids.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, pp. 251-252, Sect. 6.2.2.2, Eq. (6.2)-(6.4) and footnotes 3-4 (boundary condition b*(0) = 0)

import Definitions.Def_RevenueManagement_auctions

namespace RevenueManagement

theorem first_price_equilibrium (V : PrivateValues) (hV : V.IsRegular) (hN : 2 ≤ V.N) :
    (∀ v ∈ Set.Ioc 0 V.vbar, HasDerivWithinAt (firstPriceBid V)
        ((((V.N : ℝ) - 1) * V.F v ^ (V.N - 2) * V.f v / firstPriceWinProb V v) *
          (v - firstPriceBid V v)) (Set.Icc 0 V.vbar) v) ∧
    (∀ v ∈ Set.Icc 0 V.vbar, ∀ w ∈ Set.Icc 0 V.vbar,
      firstPriceWinProb V w * (v - firstPriceBid V w) ≤
        firstPriceWinProb V v * (v - firstPriceBid V v)) ∧
    (∀ v ∈ Set.Ioc 0 V.vbar, firstPriceBid V v < v) := by sorry

end RevenueManagement

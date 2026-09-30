-- Prove2me | Theorems.Thm_RevenueManagement_base_stock_posted_price
-- name    : RevenueManagement.base_stock_posted_price
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:49:22.402853+00:00
-- url     : https://prove2.me/theorems/f0932480-d06b-48b3-9bae-11ab050179f5
-- title:
--   Sect. 5.3.2.1: the base-stock, posted-price policy — order up to y⁰(t) and price at p(t, d⁰(t)) below it; above it order nothing and set a rate at least d⁰(t), nondecreasing in the inventory
-- statement:
--   In the pricing-and-replenishment model under its assumptions, in period $1 \le t \le T$
--   let $(y^0, d^0)$ maximize $r(t, d) - c_t\,y + G_{t+1}(y, d)$ over all $y$ and
--   $d \in [0, \bar d]$, the problem (5.20) without the constraint $y \ge x$. Then: (a) for
--   every inventory $x \le y^0$, ordering up to $y^0$ and setting the rate $d^0$ (the
--   posted price $p(t, d^0)$) is optimal in (5.20); (b) for every $x \ge y^0$ it is optimal
--   to order nothing, $y = x$, with some rate $d \ge d^0$, a price at most the posted
--   price; (c) for $y^0 \le x \le x'$, every optimal rate at $x$ with no order is matched by
--   an optimal rate at $x'$ with no order that is at least as large: the optimal rate is
--   nondecreasing in the inventory. This is the book's statement with "higher" read weakly and
--   without its interior-solution and lexicographic-selection conventions.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, pp. 213-214, Sect. 5.3.2.1 (the base-stock, posted-price policy and its footnote; Federgruen and Heching 1999 for the complete proof)

import Definitions.Def_RevenueManagement_dynamicPricing

namespace RevenueManagement

variable {Ω : Type*} [MeasurableSpace Ω]

theorem base_stock_posted_price (M : ReplPricing Ω) (hM : M.IsModel) (t : ℕ) (ht : 1 ≤ t)
    (htT : t ≤ M.T) (y0 d0 : ℝ) (hd0 : d0 ∈ Set.Icc 0 M.dbar)
    (h0 : ∀ y d, d ∈ Set.Icc 0 M.dbar → M.objective t y d ≤ M.objective t y0 d0) :
    (∀ x, x ≤ y0 → M.IsOptimal t x y0 d0) ∧
    (∀ x, y0 ≤ x → ∃ d, d0 ≤ d ∧ M.IsOptimal t x x d) ∧
    (∀ x x' d, y0 ≤ x → x ≤ x' → M.IsOptimal t x x d →
      ∃ d', d ≤ d' ∧ M.IsOptimal t x' x' d') := by sorry

end RevenueManagement

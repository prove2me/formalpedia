-- Prove2me | Theorems.Thm_RevenueManagement_reserve_price_auction_optimal
-- name    : RevenueManagement.reserve_price_auction_optimal
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:57:18.624049+00:00
-- url     : https://prove2.me/theorems/6aa31ddd-1dc2-4945-a57f-ff1324fd91fd
-- title:
--   Theorem 6.2: the C-unit second-price auction with reserve price v* (the zero of J) is an incentive-compatible mechanism whose expected revenue is at least that of every such mechanism
-- statement:
--   In the private-value $C$-unit model with regular valuations and a strictly increasing
--   virtual value $J$ with zero $v^* \in [0, \bar v]$, the standard $C$-unit second-price
--   auction with reserve price $v^*$, which awards the units to the $C$ highest valuations
--   above $v^*$ at the larger of $v^*$ and the highest losing valuation, is a feasible
--   mechanism with monotone allocations, zero surplus at zero and incentive compatibility, and
--   its expected revenue is at least that of every feasible, incentive-compatible mechanism with
--   monotone allocations and zero surplus at zero. It is optimal for the firm.
--
--   **Formalization Note** The book's Theorem 6.2 also names the first-price auction with
--   reserve price $v^*$, whose equilibrium bid (6.9) it states without proof; only the
--   second-price form is formalized, and the first-price form would follow from its own
--   equilibrium and Theorem 6.1 since both award the same allocation.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, p. 261, Theorem 6.2 ('Under the private-value models the standard C-unit first-price and second-price auctions with reserve price v* (given by (6.8)) are optimal for the firm'), second-price form

import Definitions.Def_RevenueManagement_auctions

namespace RevenueManagement

theorem reserve_price_auction_optimal (V : PrivateValues) (hV : V.IsRegular)
    (hJ : StrictMonoOn (virtualValue V) (Set.Icc 0 V.vbar)) (C : ℕ) (vstar : ℝ)
    (hvs : vstar ∈ Set.Icc 0 V.vbar) (hJ0 : virtualValue V vstar = 0) :
    ((secondPriceReserve V.N C vstar).IsFeasible C V.vbar ∧
      HasMonotoneAllocation V (secondPriceReserve V.N C vstar) ∧
      HasZeroSurplusAtZero V (secondPriceReserve V.N C vstar) ∧
      IsIncentiveCompatible V (secondPriceReserve V.N C vstar)) ∧
    ∀ M : Mechanism V.N, M.IsFeasible C V.vbar → HasMonotoneAllocation V M → HasZeroSurplusAtZero V M →
      IsIncentiveCompatible V M → expRevenue V M ≤ expRevenue V (secondPriceReserve V.N C vstar) := by sorry

end RevenueManagement

-- Prove2me | Theorems.Thm_RevenueManagement_second_price_dominant
-- name    : RevenueManagement.second_price_dominant
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:52:06.209776+00:00
-- url     : https://prove2.me/theorems/d10894fc-85e6-4714-80a3-87e33cac80c8
-- title:
--   Sect. 6.2.2.1: in the single-unit second-price auction, bidding one's own valuation is a dominant strategy, whatever the other bids
-- statement:
--   In a single-unit second-price auction where the strictly highest bid wins and pays the
--   highest other bid, a customer with valuation $v$ facing any bids of the others obtains a
--   surplus from bidding $b$ that never exceeds the surplus from bidding $v$: bidding one's
--   valuation is a dominant strategy.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, pp. 249-250, Sect. 6.2.2.1 ('the strategy b*(vi) = vi is optimal for any realization of competing bids. Such a strategy is called a dominant strategy')

import Definitions.Def_RevenueManagement_auctions

namespace RevenueManagement

theorem second_price_dominant {m : ℕ} (v b : ℝ) (others : Fin m → ℝ) :
    spSurplus v b others ≤ spSurplus v v others := by sorry

end RevenueManagement

-- Prove2me | Theorems.Thm_RevenueManagement_list_price_unconstrained_optimal
-- name    : RevenueManagement.list_price_unconstrained_optimal
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:56:56.508451+00:00
-- url     : https://prove2.me/theorems/0ef4da71-7652-4b77-be79-0163cb7c5ad4
-- title:
--   Proposition 6.1: when capacity is unconstrained (N ≤ C), a fixed list price p* with J(p*) = 0 is an optimal mechanism
-- statement:
--   In the private-value $C$-unit model with $N \le C$ customers, regular valuations and a
--   strictly increasing virtual value with zero $v^*$, the list-price mechanism at the price
--   $p^* = v^*$ (every customer with valuation above $p^*$ buys at $p^*$) earns at least the
--   expected revenue of every feasible, incentive-compatible mechanism with monotone allocations
--   and zero surplus at zero: it is an optimal mechanism for the firm.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, p. 263, Proposition 6.1 and Sect. 6.2.6.1

import Definitions.Def_RevenueManagement_auctions

namespace RevenueManagement

theorem list_price_unconstrained_optimal (V : PrivateValues) (hV : V.IsRegular)
    (hJ : StrictMonoOn (virtualValue V) (Set.Icc 0 V.vbar)) (C : ℕ) (hNC : V.N ≤ C) (vstar : ℝ)
    (hvs : vstar ∈ Set.Icc 0 V.vbar) (hJ0 : virtualValue V vstar = 0) (M : Mechanism V.N)
    (hM : M.IsFeasible C V.vbar) (hmono : HasMonotoneAllocation V M) (hzero : HasZeroSurplusAtZero V M)
    (hic : IsIncentiveCompatible V M) :
    expRevenue V M ≤ expRevenue V (listPrice V.N vstar) := by sorry

end RevenueManagement

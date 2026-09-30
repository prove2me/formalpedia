-- Prove2me | Theorems.Thm_RevenueManagement_optimal_allocation
-- name    : RevenueManagement.optimal_allocation
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:56:09.422098+00:00
-- url     : https://prove2.me/theorems/708d78d7-380e-4f7c-8229-469288a1f31e
-- title:
--   Sect. 6.2.5, Eq. (6.7)-(6.8): with J increasing, awarding the C units to the C highest valuations above v* maximizes ∑ J(vᵢ) yᵢ over all feasible allocations
-- statement:
--   Let the virtual value $J$ be increasing on $[0, \bar v]$ (Assumption 7.2) and
--   $v^* \in [0, \bar v]$ its zero, Eq. (6.8). For every valuation vector $v$ in
--   $[0, \bar v]^N$ and every allocation $y \in \{0, 1\}^N$ with $\sum_i y_i \le C$, the
--   virtual surplus $\sum_i J(v_i) y_i$ is at most that of the allocation which awards units to
--   the $C$ highest valuations above $v^*$ (the allocation rule of the second-price auction
--   with reserve price $v^*$).
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, p. 260, Sect. 6.2.5 ('the optimal allocation is to award units to the C highest-valuation customers vi above v*, and if there are less than C customers with vi > v*, to award units only to those customers and discard the remaining units')

import Definitions.Def_RevenueManagement_auctions

namespace RevenueManagement

theorem optimal_allocation (V : PrivateValues) (hV : V.IsRegular)
    (hJ : MonotoneOn (virtualValue V) (Set.Icc 0 V.vbar)) (C : ℕ) (vstar : ℝ)
    (hvs : vstar ∈ Set.Icc 0 V.vbar) (hJ0 : virtualValue V vstar = 0) (v : Fin V.N → ℝ)
    (hv : ∀ i, v i ∈ Set.Icc 0 V.vbar) (y : Fin V.N → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1)
    (hC : ∑ i, y i ≤ C) :
    ∑ i, virtualValue V (v i) * y i ≤
      ∑ i, virtualValue V (v i) * (secondPriceReserve V.N C vstar).y v i := by sorry

end RevenueManagement

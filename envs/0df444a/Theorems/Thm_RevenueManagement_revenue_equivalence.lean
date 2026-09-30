-- Prove2me | Theorems.Thm_RevenueManagement_revenue_equivalence
-- name    : RevenueManagement.revenue_equivalence
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:52:50.965087+00:00
-- url     : https://prove2.me/theorems/91cd830f-1d72-49f3-869b-17a3fd4f576c
-- title:
--   Theorem 6.1 (revenue equivalence): an incentive-compatible mechanism with monotone allocations and zero surplus at zero earns E[∑ J(vᵢ) yᵢ(v)], and expected payments are w P(w) − ∫₀ʷ P
-- statement:
--   In the private-value model with $C$ items and $N$ customers whose i.i.d. valuations have
--   a continuously differentiable, strictly increasing distribution $F$ on $[0, \bar v]$, take
--   any feasible direct mechanism that is incentive compatible and in which (i) each allocation
--   $y_i(v_i, v_{-i})$ is increasing in $v_i$ and (ii) customers with valuation zero have zero
--   expected surplus. Then the firm's expected revenue is
--   $\mathbb E[\sum_{i=1}^{N} J(v_i)\, y_i(v_i, v_{-i})]$ with $J(v) = v - (1 - F(v))/f(v)$,
--   Eq. (6.6); and each customer's expected payment is determined by the allocation alone,
--   $R_i(w) = w P_i(w) - \int_0^w P_i(s)\,ds$, the envelope identity (6.A.1) of the appendix.
-- source:
--   Kalyan T. Talluri and Garrett J. van Ryzin, The Theory and Practice of Revenue Management, Kluwer/Springer 2004, DOI 10.1007/b139000, p. 258, Theorem 6.1 with Eq. (6.6), and Appendix 6.A pp. 295-296 (Eq. 6.A.1)

import Definitions.Def_RevenueManagement_auctions

namespace RevenueManagement

theorem revenue_equivalence (V : PrivateValues) (hV : V.IsRegular) (C : ℕ) (M : Mechanism V.N)
    (hM : M.IsFeasible C V.vbar) (hmono : HasMonotoneAllocation V M) (hzero : HasZeroSurplusAtZero V M)
    (hic : IsIncentiveCompatible V M) :
    expRevenue V M = ∫ v, ∑ i, virtualValue V (v i) * M.y v i ∂V.joint ∧
    ∀ i, ∀ w ∈ Set.Icc 0 V.vbar,
      expPayment V M i w = w * winProb V M i w - ∫ s in (0 : ℝ)..w, winProb V M i s := by sorry

end RevenueManagement

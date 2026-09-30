-- Prove2me | Theorems.Thm_SupplyChainTheory_wholesale_underorder
-- name    : SupplyChainTheory.wholesale_underorder
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:26:46.320704+00:00
-- url     : https://prove2.me/theorems/c64f27b8-b76b-4578-9aff-c92b5f1a8f1d
-- title:
--   Theorem 14.2: under the wholesale price contract with $w > c_s$ the retailer under-orders, $Q^*_r < Q_0$
-- statement:
--   **Theorem 14.2.** Under the wholesale price contract, if $w > c_s$ then $Q^*_r < Q_0$: any
--   maximizer of the retailer's profit is strictly smaller than any maximizer of the chain profit.
--
--   The retailer absorbs all of the overage risk but only part of the underage risk, since the
--   supplier also pays a stockout penalty, so he orders less than the chain wants. The book omits
--   the proof (Problem 14.6): the retailer's fractile $(w + c_r - v)/(r - v + p_r)$ exceeds the
--   chain's $(c - v)/(r - v + p)$ when $w > c_s$, and $\bar F$ is nonincreasing. Only a continuous
--   distribution function and a finite mean are needed.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 570, Sect. 14.5, Theorem 14.2: 'Proof. Omitted; see Problem 14.6'

import Definitions.Def_SupplyChainTheory_contracts

namespace SupplyChainTheory

theorem wholesale_underorder (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    [MeasureTheory.NullSingletonClass D] (hD : MeasureTheory.Integrable (fun x => x) D) (w : ℝ) (hw : P.cs < w)
    (Qr Q0 : ℝ) (hr : IsMaxOn (retailerProfit P D (wholesaleTransfer w)) Set.univ Qr)
    (h0 : IsMaxOn (chainProfit P D) Set.univ Q0) : Qr < Q0 := by sorry

end SupplyChainTheory

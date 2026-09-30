-- Prove2me | Theorems.Thm_SupplyChainTheory_quantity_flex_retailer
-- name    : SupplyChainTheory.quantity_flex_retailer
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:30:59.519565+00:00
-- url     : https://prove2.me/theorems/79abb31c-51ff-4a93-91dc-614e311c6783
-- title:
--   Theorem 14.7: the quantity flexibility contract with $w(\delta)$ coordinates the retailer, $Q^*_r = Q_0$
-- statement:
--   **Theorem 14.7.** Under the quantity flexibility contract, in which the supplier reimburses
--   the retailer's loss $w + c_r - v$ on unsold units up to $\delta Q$, for any $0 \le \delta \le 1$,
--   if the wholesale price is set to $w(\delta)$ of (14.46) for the chain-optimal quantity $Q_0$,
--   then $Q_0$ maximizes the retailer's profit $\pi_r(\cdot, w(\delta), \delta)$: the supply chain is
--   coordinated from the retailer's perspective.
--
--   The book's proof shows the derivative (14.48) vanishes at $Q_0$ by the choice of $w(\delta)$
--   and that the second derivative (14.49) is nonpositive because $v - c_r \le w(\delta) \le r + p_r - c_r$.
--   The supplier's profit, by contrast, need not be maximized at $Q_0$ (the book gives a normal
--   example where $Q_0$ is a local minimum for $\delta = 0.1$), so the contract coordinates only
--   under forced compliance.
--
--   **Formalization Note** Only a continuous distribution function and finite mean are assumed:
--   the derivative $(r + p_r - w - c_r)\bar F(Q) - (w + c_r - v)(1 - \delta)F((1 - \delta)Q)$ is
--   nonincreasing without a density. At $\delta = 1$ the retailer's profit is constant in $Q$ and
--   $Q_0$ is a maximizer among equals.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 582, Sect. 14.8, Theorem 14.7 and its proof, Eq. (14.44)-(14.49); after Tsay (1999)

import Definitions.Def_SupplyChainTheory_contracts

namespace SupplyChainTheory

theorem quantity_flex_retailer (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    [MeasureTheory.NullSingletonClass D] (hD : MeasureTheory.Integrable (fun x => x) D) (delta : ℝ) (hd0 : 0 ≤ delta)
    (hd1 : delta ≤ 1) (Q0 : ℝ) (h0 : IsMaxOn (chainProfit P D) Set.univ Q0) :
    IsMaxOn (retailerProfit P D
      (quantityFlexTransfer P D (quantityFlexPrice P D Q0 delta) delta)) Set.univ Q0 := by sorry

end SupplyChainTheory

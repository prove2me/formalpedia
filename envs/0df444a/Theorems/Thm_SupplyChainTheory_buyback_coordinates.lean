-- Prove2me | Theorems.Thm_SupplyChainTheory_buyback_coordinates
-- name    : SupplyChainTheory.buyback_coordinates
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:29:56.774451+00:00
-- url     : https://prove2.me/theorems/4234c8d0-e613-4b4b-a2c0-280611e48598
-- title:
--   Theorem 14.4: the buyback contract with $w(b)$ coordinates the supply chain, $Q^*_r = Q^*_s = Q_0$
-- statement:
--   **Theorem 14.4.** Under the buyback contract, for any credit $b$ with
--   $0 \le b \le r - v + p_r$ (14.18), if the wholesale price is set to $w(b)$ of (14.22), then
--   $Q^*_r = Q^*_s = Q_0$: every maximizer of the chain profit maximizes both the retailer's and the
--   supplier's profit, every maximizer of the retailer's profit maximizes the chain profit when
--   $b < r - v + p_r$, and every maximizer of the supplier's profit maximizes the chain profit when
--   $b + p_s > 0$.
--
--   At $b = r - v + p_r$ the retailer's share $\lambda$ is $0$ and his profit is constant in $Q$,
--   so every quantity is optimal for him; likewise for the supplier when $b = p_s = 0$. Away from
--   these endpoints the maximizers coincide exactly, which is the book's reading. The result
--   follows from the identities (14.27)-(14.28) with $0 \le \lambda \le 1$; no regularity of the
--   demand beyond a finite mean is needed.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 575, Sect. 14.6, Theorem 14.4 and its two proofs, Eq. (14.18)-(14.28); after Pasternack (1985)

import Definitions.Def_SupplyChainTheory_contracts

namespace SupplyChainTheory

theorem buyback_coordinates (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    (hD : MeasureTheory.Integrable (fun x => x) D) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ P.r - P.v + P.pr) :
    (∀ Q, IsMaxOn (chainProfit P D) Set.univ Q →
        IsMaxOn (retailerProfit P D (buybackTransfer D (buybackPrice P b) b)) Set.univ Q
        ∧ IsMaxOn (supplierProfit P D (buybackTransfer D (buybackPrice P b) b)) Set.univ Q)
      ∧ (b < P.r - P.v + P.pr → ∀ Q,
          IsMaxOn (retailerProfit P D (buybackTransfer D (buybackPrice P b) b)) Set.univ Q
            → IsMaxOn (chainProfit P D) Set.univ Q)
      ∧ (0 < b + P.ps → ∀ Q,
          IsMaxOn (supplierProfit P D (buybackTransfer D (buybackPrice P b) b)) Set.univ Q
            → IsMaxOn (chainProfit P D) Set.univ Q) := by sorry

end SupplyChainTheory

-- Prove2me | Theorems.Thm_SupplyChainTheory_revenue_sharing_coordinates
-- name    : SupplyChainTheory.revenue_sharing_coordinates
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:30:34.902707+00:00
-- url     : https://prove2.me/theorems/625fb4ff-0809-41f5-ac50-a05a0c405d1d
-- title:
--   Theorem 14.6: the revenue sharing contract with $w(\phi)$ coordinates the supply chain
-- statement:
--   **Theorem 14.6.** Under the revenue sharing contract in which the retailer keeps a fraction
--   $0 \le \phi \le 1$ of his sales and salvage revenue, if the wholesale price is set to $w(\phi)$
--   of (14.34), then $Q^*_r = Q^*_s = Q_0$, i.e., the supply chain is coordinated: every maximizer
--   of the chain profit maximizes both players' profits; every maximizer of the retailer's profit
--   maximizes the chain profit when $\phi(r - v) + p_r > 0$, and every maximizer of the supplier's
--   profit does when $\phi(r - v) + p_r < r - v + p$.
--
--   The proof is the $\lambda$-argument of Theorem 14.4 with
--   $\lambda = (\phi(r - v) + p_r)/(r - v + p)$ of (14.36): the retailer's profit is
--   $\lambda\Pi(Q) + \mu(\lambda p - p_r)$ and the supplier's is the complement. The book notes
--   that revenue sharing with $(w, \phi)$ is equivalent to buyback with $w_b = w + (1 - \phi)r$ and
--   $b = (1 - \phi)(r - v)$.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 579, Sect. 14.7, Theorem 14.6 and its proof, Eq. (14.33)-(14.39); after Cachon and Lariviere (2005)

import Definitions.Def_SupplyChainTheory_contracts

namespace SupplyChainTheory

theorem revenue_sharing_coordinates (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    (hD : MeasureTheory.Integrable (fun x => x) D) (phi : ℝ) (h0 : 0 ≤ phi) (h1 : phi ≤ 1) :
    (∀ Q, IsMaxOn (chainProfit P D) Set.univ Q →
        IsMaxOn (retailerProfit P D (revenueShareTransfer P D (revenueSharePrice P phi) phi))
          Set.univ Q
        ∧ IsMaxOn (supplierProfit P D (revenueShareTransfer P D (revenueSharePrice P phi) phi))
          Set.univ Q)
      ∧ (0 < phi * (P.r - P.v) + P.pr → ∀ Q,
          IsMaxOn (retailerProfit P D (revenueShareTransfer P D (revenueSharePrice P phi) phi))
            Set.univ Q → IsMaxOn (chainProfit P D) Set.univ Q)
      ∧ (phi * (P.r - P.v) + P.pr < P.r - P.v + P.p → ∀ Q,
          IsMaxOn (supplierProfit P D (revenueShareTransfer P D (revenueSharePrice P phi) phi))
            Set.univ Q → IsMaxOn (chainProfit P D) Set.univ Q) := by sorry

end SupplyChainTheory

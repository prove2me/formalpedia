-- Prove2me | Theorems.Thm_SupplyChainTheory_buyback_profit_identities
-- name    : SupplyChainTheory.buyback_profit_identities
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:29:05.217317+00:00
-- url     : https://prove2.me/theorems/ec482dbe-8d52-40aa-a8d7-0242503d91b8
-- title:
--   Eq. (14.27)-(14.28): under the buyback contract with $w(b)$, $\pi_r = \lambda\Pi + \mu(\lambda p - p_r)$ and $\pi_s = (1 - \lambda)\Pi - \mu(\lambda p - p_r)$
-- statement:
--   Under the buyback contract with credit $b$ and wholesale price $w(b)$ of (14.22), with
--   $\lambda = (r - v + p_r - b)/(r - v + p)$ as in (14.25), for every order quantity $Q$,
--
--   $$ \pi_r(Q, w(b), b) = \lambda\,\Pi(Q) + \mu(\lambda p - p_r), \qquad
--      \pi_s(Q, w(b), b) = (1 - \lambda)\,\Pi(Q) - \mu(\lambda p - p_r). $$
--
--   This is the second proof of Theorem 14.4: the definition of $w(b)$ makes $\lambda$ equal
--   both to (14.25) and to (14.26), so the retailer's profit is an affine function of the chain
--   profit with a nonnegative slope, and the supplier's is the complement. The identities hold for
--   every $b$ and every demand law with finite mean; $\lambda$ is the retailer's share of the
--   chain profit, and the range $0 \le \lambda \le 1$ is where both players' interests point the
--   same way as the chain's.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 576, Sect. 14.6, Proof #2 of Theorem 14.4, Eq. (14.25)-(14.28)

import Definitions.Def_SupplyChainTheory_contracts

namespace SupplyChainTheory

theorem buyback_profit_identities (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    (hD : MeasureTheory.Integrable (fun x => x) D) (b Q : ℝ) :
    retailerProfit P D (buybackTransfer D (buybackPrice P b) b) Q
        = buybackShare P b * chainProfit P D Q
          + meanDemand D * (buybackShare P b * P.p - P.pr)
      ∧ supplierProfit P D (buybackTransfer D (buybackPrice P b) b) Q
        = (1 - buybackShare P b) * chainProfit P D Q
          - meanDemand D * (buybackShare P b * P.p - P.pr) := by sorry

end SupplyChainTheory

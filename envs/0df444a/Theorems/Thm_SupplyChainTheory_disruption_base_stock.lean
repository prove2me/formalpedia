-- Prove2me | Theorems.Thm_SupplyChainTheory_disruption_base_stock
-- name    : SupplyChainTheory.disruption_base_stock
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:48:53.8707+00:00
-- url     : https://prove2.me/theorems/06495112-47b5-4777-8cdc-d62ed900f245
-- title:
--   Theorem 9.5: the optimal base-stock level with disruptions is $S^* = d + d\,F^{-1}(p/(p+h))$
-- statement:
--   **Theorem 9.5.** In the infinite-horizon newsvendor problem with deterministic demand $d > 0$
--   per period and supply disruptions with disruption probability $\alpha$ and recovery probability
--   $\beta$ ($0 < \alpha, \beta \le 1$), holding cost $h > 0$ and backorder cost $p > 0$, the optimal
--   base-stock level is
--
--   $$ S^* \;=\; d + d\,F^{-1}\Big(\frac{p}{p+h}\Big), $$
--
--   where $F$ is the distribution function (9.10) of the disruption length and $F^{-1}(\gamma)$ is
--   the smallest $n$ with $F(n) \ge \gamma$. Formally, for the $k$ with $F(k) \ge p/(p+h)$ and
--   $F(n) < p/(p+h)$ for all $n < k$, the level $d + dk$ minimizes $g$ and is its least minimizer.
--
--   The book's derivation: the finite difference $\Delta g(S) = g(S+d) - g(S)$ at a multiple $S$ of
--   $d$ equals $d[(h+p)F(S/d - 1) - p]$, so $S^*$ is the smallest multiple of $d$ at which this is
--   nonnegative. The formula mirrors the demand-uncertainty newsvendor solution
--   $S^* = \mu + \sigma\Phi^{-1}(p/(p+h))$: $d$ is cycle stock, $dF^{-1}(\gamma)$ is safety stock
--   protecting against disruptions of up to $F^{-1}(\gamma)$ periods, and $\gamma$ is the type-1
--   service level. In Example 9.3, $\gamma = 0.9231$, $F^{-1}(\gamma) = 3$ and $S^* = 8000$.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, pp. 363-364, Sect. 9.2.2.4, Theorem 9.5, Eq. (9.15)-(9.18) and the derivation of ∆g(S); after Tomlin (2006)

import Definitions.Def_SupplyChainTheory_disruptions

namespace SupplyChainTheory

theorem disruption_base_stock (α β h p d : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (hh : 0 < h) (hp : 0 < p) (hd : 0 < d) (k : ℕ)
    (hk : p / (p + h) ≤ disruptionCdf α β k) (hk' : ∀ n < k, disruptionCdf α β n < p / (p + h)) :
    IsMinOn (meanCost α β h p d) Set.univ (d + d * k)
      ∧ ∀ S, IsMinOn (meanCost α β h p d) Set.univ S → d + d * k ≤ S := by sorry

end SupplyChainTheory

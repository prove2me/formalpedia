-- Prove2me | Theorems.Thm_RevShareCoord_Competing_cournot_supplier_optimal_price
-- name    : RevShareCoord.Competing.cournot_supplier_optimal_price
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T00:53:28.035989+00:00
-- url     : https://prove2.me/theorems/0c4bc1eb-6b88-4146-9920-24645f42dc5d
-- title:
--   Sec. 4.1.2 — Cournot: the supplier's optimal wholesale price is w* = (1 + c)/2, and w* − w^I = (1 − c)/(2 + 2β(n − 1))
-- statement:
--   Let $n \ge 1$ symmetric retailers have the Cournot revenues $R_i(\bar q) = q_i(1 - q_i - \beta\sum_{j\ne i} q_j)$ with $0\le\beta<1$, let the unit cost satisfy $0<c<1$, and let the supplier charge every retailer the same wholesale price $w$, with no revenue sharing. Her profit at an equilibrium $\bar q$ of the retailers' game is $\sum_i (w-c) q_i$. Let
--   $$w^* = \frac{1+c}{2}.$$
--   Then:
--
--   1. the symmetric profile $q_i^N(w^*) = (1-w^*)/(2+\beta(n-1))$ is a Nash equilibrium at $w^*$;
--   2. for every price $w > 0$ and every Nash equilibrium $\bar q$ of the retailers' game at $w$, the supplier's profit is at most her profit at $w^*$ with $\bar q^N(w^*)$, and strictly less when $w \neq w^*$; so $w^*$ is her optimal wholesale price, and it does not depend on $\beta$ or $n$;
--   3. the gap between $w^*$ and the coordinating price $w^I$ is
--   $$w^* - w^I = \frac{1-c}{2+2\beta(n-1)},$$
--   which vanishes as $n$ grows.
--
--   **Formalization Note** "$n$ symmetric retailers" is read as a common wholesale price for all retailers; the supplier optimizes over that common price. The supplier anticipates the retailers' equilibrium response, and the comparison is over every equilibrium at every price $w > 0$.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), pp. 19–20 (PDF pp. 20–21), Section 4.1.2, last paragraph of p. 19 and first sentence of p. 20

import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Cournot

namespace RevShareCoord.Competing

/-- **Sec. 4.1.2, the supplier's optimal wholesale price (pp. 19–20).** Cournot revenues (7) with
`0 ≤ β < 1`, `n ≥ 1` symmetric retailers, unit cost `0 < c < 1`, a common wholesale price and no
revenue sharing. Let `w* = (1 + c)/2`.
1. The symmetric profile `q_i^N(w*) = (1 − w*)/(2 + β(n − 1))` is a Nash equilibrium at `w*`.
2. For every price `w > 0` and every Nash equilibrium `q̄` at `w`, the supplier's profit
   `Σᵢ (w − c) qᵢ` is at most her profit at `w*` with `q̄^N(w*)`, and strictly less if `w ≠ w*`.
3. The gap `w* − w^I` equals `(1 − c)/(2 + 2β(n − 1))`. -/
theorem cournot_supplier_optimal_price {n : ℕ} (β c : ℝ) (hn : 1 ≤ n) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hc0 : 0 < c) (hc1 : c < 1) :
    IsNashEquilibrium (cournotRevenue β) 1 (fun _ : Fin n => (1 + c) / 2)
        (fun _ => cournotQN β n ((1 + c) / 2)) ∧
      (∀ w : ℝ, 0 < w → ∀ q : Fin n → ℝ,
        IsNashEquilibrium (cournotRevenue β) 1 (fun _ => w) q →
          supplierProfit (cournotRevenue β) c 1 (fun _ => w) q ≤
              supplierProfit (cournotRevenue β) c 1 (fun _ : Fin n => (1 + c) / 2)
                (fun _ => cournotQN β n ((1 + c) / 2)) ∧
            (w ≠ (1 + c) / 2 →
              supplierProfit (cournotRevenue β) c 1 (fun _ => w) q <
                supplierProfit (cournotRevenue β) c 1 (fun _ : Fin n => (1 + c) / 2)
                  (fun _ => cournotQN β n ((1 + c) / 2)))) ∧
      (1 + c) / 2 - cournotWI β n c = (1 - c) / (2 + 2 * β * ((n : ℝ) - 1)) := by sorry

end RevShareCoord.Competing

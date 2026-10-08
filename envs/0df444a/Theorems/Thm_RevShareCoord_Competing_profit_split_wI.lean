-- Prove2me | Theorems.Thm_RevShareCoord_Competing_profit_split_wI
-- name    : RevShareCoord.Competing.profit_split_wI
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:17:35.902703+00:00
-- url     : https://prove2.me/theorems/37c5b219-7d06-4c7f-8685-8b4a96f6cdf4
-- title:
--   Sec. 3.2 — under w̄^I the supplier earns Σ_i q_i^I Σ_{j≠i} (−R_j^i(q̄^I)) and retailer i earns R_i(q̄^I) − q_i^I w_i^I
-- statement:
--   In the competing-retailers model, let the supplier charge the coordinating wholesale prices $w_i^I = c - \sum_{j\neq i} R_j^i(\bar q^I)$ (no revenue sharing), where $R_j^i = \partial R_j/\partial q_i$. At the profile $\bar q^I$ the profits are
--   $$\pi_s(\bar q^I, \bar w^I) = \sum_{i=1}^n q_i^I \sum_{j\neq i} -R_j^i(\bar q^I),$$
--   $$\pi_{r_i}(\bar q^I, \bar w^I) = R_i(\bar q^I) - q_i^I w_i^I, \qquad i = 1,\dots,n.$$
--
--   The supplier's margin is exactly the externality charge collected from every retailer. Because $\bar w^I$ is pinned down by the coordination requirement, this is the only division of the system profit that wholesale prices alone can support.
--
--   **Formalization Note** The identities hold at any profile $\bar q^I$ at which $\bar w^I$ is computed; no equilibrium property is used. The second line is the definition of the retailer's wholesale-price profit, included because the page displays it as part of the division of profits.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 14 (PDF p. 15), Section 3.2, first display

import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Model

namespace RevShareCoord.Competing

open Finset

/-- **Sec. 3.2, the division of profits under `w̄^I` (p. 14).** Index convention:
`M.dR i j q = R_j^i(q̄) = ∂R_j/∂q_i`. Under the wholesale prices `w_i^I = c − Σ_{j≠i} R_j^i(q̄^I)`
(`φ = 1`), at the profile `q̄^I` the supplier earns
`π_s(q̄^I, w̄^I) = Σᵢ q_i^I Σ_{j≠i} (−R_j^i(q̄^I))`, and retailer `i` earns
`π_{rᵢ}(q̄^I, w̄^I) = Rᵢ(q̄^I) − q_i^I w_i^I`. -/
theorem profit_split_wI {n : ℕ} (M : Model n) (qI : Fin n → ℝ) :
    supplierProfit M.R M.c 1 (M.wI qI) qI =
        ∑ i, qI i * ∑ j ∈ univ.erase i, (-M.dR i j qI) ∧
      ∀ i, retailerProfit M.R 1 (M.wI qI) qI i = M.R i qI - qI i * M.wI qI i := by sorry

end RevShareCoord.Competing

-- Prove2me | Theorems.Thm_RevShareCoord_Competing_retailer_participation
-- name    : RevShareCoord.Competing.retailer_participation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:17:43.477546+00:00
-- url     : https://prove2.me/theorems/bcf8a46c-a74e-45db-8af0-718162430850
-- title:
--   Sec. 3.2 — π_{r_i}(q̄^I, w̄^I) ≥ 0: every retailer earns a nonnegative profit at the coordinating prices
-- statement:
--   In the competing-retailers model, let $\bar q^I$ have positive entries and solve the integrated first-order system (6), and let $w_i^I = c - \sum_{j\neq i} R_j^i(\bar q^I)$ be the coordinating wholesale prices. Assume that a location that stocks nothing earns nonnegative revenue: $R_i$ evaluated at $\bar q^I$ with $q_i$ replaced by $0$ is $\ge 0$, for every $i$. Then every retailer's profit under the wholesale prices $\bar w^I$ is nonnegative,
--   $$\pi_{r_i}(\bar q^I, \bar w^I) = R_i(\bar q^I) - q_i^I w_i^I \ge 0, \qquad i=1,\dots,n.$$
--
--   Since revenue sharing with $(\phi, \phi\bar w^I)$ gives retailer $i$ the profit $\phi\,\pi_{r_i}(\bar q^I, \bar w^I)$, every retailer is then willing to participate for any $\phi \ge 0$.
--
--   **Formalization Note** The page states "It can be shown that $\pi_{r_i}(\bar q^I, \bar w^I) \ge 0$" without proof or further hypothesis. With concavity of $R_i$ in $q_i$ (the model's reading of unimodality) the claim also needs a lower bound on revenue at zero stock; nonnegative revenue at a location that stocks nothing is the weakest natural such condition (it holds in the Cournot example (7), where that revenue is $0$), and it is added as a hypothesis.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 14 (PDF p. 15), Section 3.2, sentence after the display of π_{r_i}(q̄^I, φ, φw̄^I)

import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Model

namespace RevShareCoord.Competing

open Finset

/-- **Sec. 3.2, participation under `w̄^I` (p. 14).** Index convention:
`M.dR i j q = R_j^i(q̄) = ∂R_j/∂q_i`. Let `q̄^I` have positive entries and solve (6). Assume that a
location stocking nothing earns nonnegative revenue: `Rᵢ(q̄^I with qᵢ replaced by 0) ≥ 0`. Then
every retailer earns a nonnegative profit under the wholesale prices `w̄^I`:
`π_{rᵢ}(q̄^I, w̄^I) = Rᵢ(q̄^I) − q_i^I w_i^I ≥ 0`. -/
theorem retailer_participation {n : ℕ} (M : Model n) (qI : Fin n → ℝ)
    (hpos : ∀ i, 0 < qI i) (hfoc : M.FOC qI)
    (hzero : ∀ i, 0 ≤ M.R i (Function.update qI i 0)) :
    ∀ i, 0 ≤ retailerProfit M.R 1 (M.wI qI) qI i := by sorry

end RevShareCoord.Competing

-- Prove2me | Theorems.Thm_RevShareCoord_Competing_revenue_sharing_profit_identities
-- name    : RevShareCoord.Competing.revenue_sharing_profit_identities
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:17:47.393513+00:00
-- url     : https://prove2.me/theorems/6d7c2156-2091-4a77-b3b2-8b79bff3696f
-- title:
--   Sec. 3.2 — under (φ, φw̄^I): π_{r_i} = φπ_{r_i}(q̄^I, w̄^I) and π_s = (1 − φ)Π(q̄^I) + φπ_s(q̄^I, w̄^I)
-- statement:
--   In the competing-retailers model, let $w_i^I = c - \sum_{j\neq i} R_j^i(\bar q^I)$ be the coordinating wholesale prices at a profile $\bar q^I$, and let the supplier offer retailer $i$ the revenue-sharing contract $(\phi, \phi w_i^I)$. Then for every $\phi$, at the profile $\bar q^I$:
--
--   1. each retailer's profit is the fraction $\phi$ of its wholesale-price profit,
--   $$\pi_{r_i}(\bar q^I, \phi, \phi\bar w^I) = \phi\big(R_i(\bar q^I) - q_i^I w_i^I\big) = \phi\,\pi_{r_i}(\bar q^I, \bar w^I);$$
--   2. the supplier's profit is a convex combination (for $\phi\in[0,1]$) of the integrated system profit and what she earns without revenue sharing,
--   $$\pi_s(\bar q^I, \phi, \phi\bar w^I) = (1-\phi)\,\Pi(\bar q^I) + \phi\,\pi_s(\bar q^I, \bar w^I).$$
--
--   Together with the equilibrium property of $\bar q^I$, these identities show that revenue sharing can implement any split of the system profit between the supplier and the competing retailers along this line.
--
--   **Formalization Note** The page writes $\phi(R_i(\bar q^I) - q_i^I w_i)$; the $w_i$ there is $w_i^I$ (the superscript is dropped on the page), and the Lean statement uses $w_i^I$. Both identities are algebraic and hold for every real $\phi$ and every profile.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 14 (PDF p. 15), Section 3.2, displays for π_{r_i}(q̄^I, φ, φw̄^I) and π_s(q̄^I, φ, φw̄^I)

import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Model

namespace RevShareCoord.Competing

open Finset

/-- **Sec. 3.2, profits under the contracts `(φ, φ w̄^I)` (p. 14).** Index convention:
`M.dR i j q = R_j^i(q̄) = ∂R_j/∂q_i`. For every `φ`, with `wᵢ(φ) = φ w_i^I`, at the profile
`q̄^I`:
1. `π_{rᵢ}(q̄^I, φ, φ w̄^I) = φ π_{rᵢ}(q̄^I, w̄^I)` for every retailer `i`;
2. `π_s(q̄^I, φ, φ w̄^I) = (1 − φ) Π(q̄^I) + φ π_s(q̄^I, w̄^I)`. -/
theorem revenue_sharing_profit_identities {n : ℕ} (M : Model n) (qI : Fin n → ℝ) (φ : ℝ) :
    (∀ i, retailerProfit M.R φ (fun k => φ * M.wI qI k) qI i =
        φ * retailerProfit M.R 1 (M.wI qI) qI i) ∧
      supplierProfit M.R M.c φ (fun k => φ * M.wI qI k) qI =
        (1 - φ) * systemProfit M.R M.c qI + φ * supplierProfit M.R M.c 1 (M.wI qI) qI := by sorry

end RevShareCoord.Competing

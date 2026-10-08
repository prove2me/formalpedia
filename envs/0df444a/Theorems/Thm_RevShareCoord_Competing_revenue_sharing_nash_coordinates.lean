-- Prove2me | Theorems.Thm_RevShareCoord_Competing_revenue_sharing_nash_coordinates
-- name    : RevShareCoord.Competing.revenue_sharing_nash_coordinates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:17:52.106984+00:00
-- url     : https://prove2.me/theorems/6c3865ea-cfdc-43c1-883f-6890b5c1b36b
-- title:
--   Sec. 3.2 — with w_i(φ) = φw_i^I, q̄^I is a Nash equilibrium, retailer i earns φπ_{r_i}(q̄^I, w̄^I) and the supplier (1 − φ)Π(q̄^I) + φπ_s(q̄^I, w̄^I)
-- statement:
--   A single supplier with unit cost $c > 0$ sells through $n$ competing retailers, location $i$ earning revenue $R_i(\bar q)$ from the stocking profile $\bar q$, under the standing assumptions of Section 3.2. Write $R_j^i = \partial R_j/\partial q_i$. Let $\bar q^I$ have positive entries and solve the integrated first-order system (6),
--   $$R_i^i(\bar q^I) + \sum_{j\neq i} R_j^i(\bar q^I) = c, \qquad i = 1,\dots,n .$$
--   Let $\phi \in [0,1]$, and let the supplier offer retailer $i$ the revenue-sharing contract $(\phi, w_i(\phi))$ with
--   $$w_i(\phi) = \phi w_i^I = \phi\Big(c - \sum_{j\neq i} R_j^i(\bar q^I)\Big).$$
--   Then:
--
--   1. $\bar q^I$ is a Nash equilibrium in order quantities of the retailers' game;
--   2. retailer $i$ earns $\pi_{r_i}(\bar q^I, \phi, \phi \bar w^I) = \phi\,\pi_{r_i}(\bar q^I, \bar w^I)$;
--   3. the supplier earns
--   $$\pi_s(\bar q^I, \phi, \phi\bar w^I) = (1-\phi)\,\Pi(\bar q^I) + \phi\,\pi_s(\bar q^I, \bar w^I),$$
--   a convex combination of the integrated system profit and what she would earn without revenue sharing.
--
--   So revenue sharing coordinates the competing-retailers channel just as it does a single retailer, and the parameter $\phi$ moves the supplier's share of the system profit along a line.
--
--   **Formalization Note** "Unimodal in $q_i$" is read as concavity of $R_i$ in its own quantity (see the model definition); this is the hypothesis that makes the retailer's first-order condition sufficient, which the page's equilibrium argument relies on. $\bar q^I$ is any positive solution of (6); the page's system optimum is one by its standing assumption, and its optimality is not used. The page writes $\phi(R_i(\bar q^I) - q_i^I w_i)$, where $w_i$ is $w_i^I$. At $\phi = 0$ the equilibrium claim holds trivially (all retailer profits vanish), as on the page, which allows $\phi \in [0,1]$.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 14 (PDF p. 15), Section 3.2, paragraph 'Suppose the supplier now offers retailer i a revenue-sharing contract' through 'what she would earn without revenue sharing'

import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Model

namespace RevShareCoord.Competing

open Finset

/-- **Sec. 3.2, revenue sharing with competing retailers (p. 14).** Index convention:
`M.dR i j q = R_j^i(q̄) = ∂R_j/∂q_i`. Let `q̄^I` have positive entries and solve the first-order
system (6) of the integrated channel. Let `φ ∈ [0, 1]`, and let the supplier offer retailer `i`
the revenue-sharing contract `(φ, wᵢ(φ))` with `wᵢ(φ) = φ w_i^I = φ (c − Σ_{j≠i} R_j^i(q̄^I))`.
Then
1. `q̄^I` is a Nash equilibrium of the retailers' quantity game;
2. each retailer earns `π_{rᵢ}(q̄^I, φ, φ w̄^I) = φ π_{rᵢ}(q̄^I, w̄^I)`;
3. the supplier earns `π_s(q̄^I, φ, φ w̄^I) = (1 − φ) Π(q̄^I) + φ π_s(q̄^I, w̄^I)`. -/
theorem revenue_sharing_nash_coordinates {n : ℕ} (M : Model n) (qI : Fin n → ℝ)
    (hpos : ∀ i, 0 < qI i) (hfoc : M.FOC qI) (φ : ℝ) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) :
    IsNashEquilibrium M.R φ (fun k => φ * M.wI qI k) qI ∧
      (∀ i, retailerProfit M.R φ (fun k => φ * M.wI qI k) qI i =
        φ * retailerProfit M.R 1 (M.wI qI) qI i) ∧
      supplierProfit M.R M.c φ (fun k => φ * M.wI qI k) qI =
        (1 - φ) * systemProfit M.R M.c qI + φ * supplierProfit M.R M.c 1 (M.wI qI) qI := by sorry

end RevShareCoord.Competing

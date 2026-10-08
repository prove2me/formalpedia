-- Prove2me | Theorems.Thm_RevShareCoord_Competing_revenue_sharing_equilibrium_foc
-- name    : RevShareCoord.Competing.revenue_sharing_equilibrium_foc
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:17:40.436725+00:00
-- url     : https://prove2.me/theorems/c999c39d-e3ec-482a-8a30-3fef996a3524
-- title:
--   Sec. 3.2 — under revenue sharing (φ, w_i(φ)), an interior equilibrium satisfies φR_i^i(q̄^N) = w_i(φ)
-- statement:
--   In the competing-retailers model, let $\phi \in [0,1]$ and let the supplier offer retailer $i$ the revenue-sharing contract $(\phi, w_i(\phi))$: retailer $i$ pays $w_i(\phi)$ per unit and keeps the fraction $\phi$ of its revenue, so its profit is $\phi R_i(\bar q) - w_i(\phi) q_i$. Then every Nash equilibrium $\bar q^N$ in order quantities with all entries positive satisfies
--   $$\phi R_i^i(\bar q^N) = w_i(\phi), \qquad i = 1,\dots,n,$$
--   where $R_i^i = \partial R_i/\partial q_i$.
--
--   This is the revenue-sharing analogue of Equation (8), and it is the condition that determines which prices make a given profile an equilibrium.
--
--   **Formalization Note** The prices $w_i(\phi)$ are arbitrary real numbers; the conclusion uses only that $\bar q^N$ is an interior equilibrium and that $R_i$ is differentiable in $q_i$ at positive profiles.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 14 (PDF p. 15), Section 3.2, display φR_i^i(q̄^N) = w_i(φ)

import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Model

namespace RevShareCoord.Competing

open Finset

/-- **Sec. 3.2, equilibrium condition under revenue sharing (p. 14).** Index convention:
`M.dR i j q = R_j^i(q̄) = ∂R_j/∂q_i`. Let `φ ∈ [0, 1]` and let retailer `i` be offered the
revenue-sharing contract `(φ, wᵢ(φ))`. Every Nash equilibrium `q̄^N` of the retailers' game with
all entries positive satisfies `φ R_i^i(q̄^N) = wᵢ(φ)` for `i = 1, …, n`. -/
theorem revenue_sharing_equilibrium_foc {n : ℕ} (M : Model n) (φ : ℝ)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (w : Fin n → ℝ) (qN : Fin n → ℝ)
    (hN : IsNashEquilibrium M.R φ w qN) (hpos : ∀ i, 0 < qN i) :
    ∀ i, φ * M.dR i i qN = w i := by sorry

end RevShareCoord.Competing

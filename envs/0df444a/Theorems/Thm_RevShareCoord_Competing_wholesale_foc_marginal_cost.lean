-- Prove2me | Theorems.Thm_RevShareCoord_Competing_wholesale_foc_marginal_cost
-- name    : RevShareCoord.Competing.wholesale_foc_marginal_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:17:17.363985+00:00
-- url     : https://prove2.me/theorems/06c31857-9540-44d8-8248-9055b675e090
-- title:
--   Sec. 3.2, Eq. (8) — R_i^i(q̄^N) = w_i at an interior equilibrium; q̄^I is not an equilibrium at marginal-cost prices
-- statement:
--   Consider the competing-retailers model with revenue functions $R_i$, unit cost $c$ and $R_j^i = \partial R_j/\partial q_i$, under wholesale-price contracts (no revenue sharing).
--
--   1. **Equation (8).** Let the supplier charge retailer $i$ the price $w_i > 0$. Every Nash equilibrium $\bar q^N$ in order quantities whose entries are all positive satisfies
--   $$R_i^i(\bar q^N) = w_i, \qquad i = 1,\dots,n.$$
--   2. **Marginal-cost pricing fails.** Let $\bar q^I$ have positive entries and solve the integrated first-order system (6). If for some $i$ the externality of location $i$ is negative, $\sum_{j\neq i} R_j^i(\bar q^I) < 0$, then $R_i^i(\bar q^I) > c$, and $\bar q^I$ is not a Nash equilibrium when every retailer pays the marginal cost $w_j = c$: retailer $i$ gains by ordering more.
--
--   Comparing (8) with (6) shows that a decentralized retailer ignores the externality $\sum_{j\neq i} R_j^i$ it imposes on the other locations.
--
--   **Formalization Note** The page asserts $R_i^i(\bar q^I) > c$ without a condition. It requires some negative cross-effect $R_j^i(\bar q^I) < 0$; with all cross-effects zero it is false, so part 2 carries this as a hypothesis. $\bar q^I$ is taken as any positive solution of (6), which by the paper's standing assumption includes the system optimum.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 13 (PDF p. 14), Section 3.2, Eq. (8) and the following paragraph

import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Model

namespace RevShareCoord.Competing

open Finset

/-- **Sec. 3.2, Eq. (8) and marginal-cost pricing (p. 13).** Index convention:
`M.dR i j q = R_j^i(q̄) = ∂R_j/∂q_i`.

1. Under wholesale prices `w̄` (`φ = 1`), every Nash equilibrium `q̄^N` with all entries positive
   satisfies `R_i^i(q̄^N) = wᵢ` for every `i` (Eq. (8)).
2. Let `q̄^I` have positive entries and solve (6). If location `i` imposes a negative externality
   at `q̄^I`, `Σ_{j≠i} R_j^i(q̄^I) < 0`, then `R_i^i(q̄^I) > c`, and `q̄^I` is not a Nash equilibrium
   when the supplier charges every retailer the marginal cost `c`. -/
theorem wholesale_foc_marginal_cost {n : ℕ} (M : Model n) :
    (∀ (w : Fin n → ℝ) (qN : Fin n → ℝ), (∀ i, 0 < w i) →
        IsNashEquilibrium M.R 1 w qN → (∀ i, 0 < qN i) → ∀ i, M.dR i i qN = w i) ∧
    (∀ qI : Fin n → ℝ, (∀ i, 0 < qI i) → M.FOC qI →
        ∀ i, ∑ j ∈ univ.erase i, M.dR i j qI < 0 →
          M.c < M.dR i i qI ∧ ¬ IsNashEquilibrium M.R 1 (fun _ => M.c) qI) := by sorry

end RevShareCoord.Competing

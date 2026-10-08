-- Prove2me | Theorems.Thm_RevShareCoord_Competing_coordinating_wholesale_nash
-- name    : RevShareCoord.Competing.coordinating_wholesale_nash
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:17:29.322582+00:00
-- url     : https://prove2.me/theorems/4f85fa16-904c-4c63-ad6d-b12333c4e6ca
-- title:
--   Sec. 3.2 — at the wholesale prices w_i^I = c − Σ_{j≠i} R_j^i(q̄^I), q̄^I is a Nash equilibrium
-- statement:
--   In the competing-retailers model, let $\bar q^I$ be a profile with all entries positive that solves the integrated first-order system (6),
--   $$R_i^i(\bar q^I) + \sum_{j\neq i} R_j^i(\bar q^I) = c, \qquad i=1,\dots,n,$$
--   where $R_j^i = \partial R_j/\partial q_i$. Suppose the supplier charges retailer $i$ the wholesale price
--   $$w_i^I = c - \sum_{j\neq i} R_j^i(\bar q^I)$$
--   and shares no revenue. Then $\bar q^I$ is a Nash equilibrium in order quantities of the retailers' game: no retailer can raise its profit $R_i(\bar q) - w_i^I q_i$ by changing its own quantity to any nonnegative value.
--
--   The prices $w^I_i$ charge each retailer for the marginal cost it imposes on the system, both in production and through competition, and so decentralize the system-optimal quantities.
--
--   **Formalization Note** The page writes "$\bar q^*$ is a Nash equilibrium"; from the context ($\bar q^*$ is not defined in Section 3.2 and the two systems (8) and (6) are said to coincide) this is $\bar q^I$. $\bar q^I$ is taken as any positive solution of (6); the paper's system optimum is such a profile by its standing assumption.
-- source:
--   Cachon, Lariviere, Supply Chain Coordination with Revenue-Sharing Contracts: Strengths and Limitations, working paper (June 2000), p. 13 (PDF p. 14), Section 3.2, display defining w_i^I and the sentence after it

import Mathlib
import Definitions.Def_RevShareCoord_Competing_Game
import Definitions.Def_RevShareCoord_Competing_Model

namespace RevShareCoord.Competing

open Finset

/-- **Sec. 3.2, the coordinating wholesale prices (p. 13).** Index convention:
`M.dR i j q = R_j^i(q̄) = ∂R_j/∂q_i`. Let `q̄^I` have positive entries and solve the first-order
system (6), `R_i^i(q̄^I) + Σ_{j≠i} R_j^i(q̄^I) = c`. If the supplier charges retailer `i` the
wholesale price `w_i^I = c − Σ_{j≠i} R_j^i(q̄^I)` (no revenue sharing, `φ = 1`), then `q̄^I` is a
Nash equilibrium of the retailers' quantity game. -/
theorem coordinating_wholesale_nash {n : ℕ} (M : Model n) (qI : Fin n → ℝ)
    (hpos : ∀ i, 0 < qI i) (hfoc : M.FOC qI) :
    IsNashEquilibrium M.R 1 (M.wI qI) qI := by sorry

end RevShareCoord.Competing

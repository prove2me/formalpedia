-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_matching_card_le_half
-- name    : QuantumMaxCutEnergy.matching_card_le_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T05:07:29.281158+00:00
-- url     : https://prove2.me/theorems/d38e7290-b2ed-48a4-b51f-2294ac3b14a4
-- title:
--   A matching has at most half as many edges as there are vertices
-- statement:
--   **A matching has at most half as many edges as there are vertices.**
--
--   For a graph on $n$ vertices and a set $M$ of pairwise disjoint edges,
--   $$2\,|M|\;\le\; n,$$
--   because the $2|M|$ endpoints of the edges of $M$ are distinct vertices.
--
--   **Role.** This is the counting fact behind every odd-set argument on the matching polytope: it is what makes
--   the odd-set constraint $\sum_{e\subseteq S}x_e\le(|S|-1)/2$ a *tight* description of the matchings rather than
--   merely a valid one, and it is what shows that a point concentrated on too many edges cannot be dominated by an
--   integral matching (see `QuantumMaxCutEnergy.loads_insufficient_on_five`).
-- source:
--   Edmonds, J. Res. Nat. Bur. Standards 69B (1965); standard counting behind the odd-set constraints of the matching polytope.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- A matching has at most half as many edges as there are vertices. -/
theorem matching_card_le_half {n : ℕ} (M : Finset (Edge n))
    (hM : ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
      e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2) :
    2 * M.card ≤ n := by sorry

end QuantumMaxCutEnergy

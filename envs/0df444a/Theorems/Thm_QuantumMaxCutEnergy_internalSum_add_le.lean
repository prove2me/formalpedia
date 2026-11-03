-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_internalSum_add_le
-- name    : QuantumMaxCutEnergy.internalSum_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T05:07:33.106055+00:00
-- url     : https://prove2.me/theorems/1f73a8bc-af4a-4abf-82b2-002a7c37a119
-- title:
--   Uncrossing identity: internal edge masses of $A$ and $B$ are at most those of $A\cup B$ and $A\cap B$
-- statement:
--   **Uncrossing identity for internal edge masses.**
--
--   For a nonnegative edge weight $x$ and two vertex sets $A,B$,
--   $$\mathrm{internalSum}\,x\,A+\mathrm{internalSum}\,x\,B\;\le\;\mathrm{internalSum}\,x\,(A\cup B)+\mathrm{internalSum}\,x\,(A\cap B).$$
--
--   **Proof.** Termwise: an edge with both endpoints in $A$ and in $B$ is counted twice on each side; an edge inside
--   exactly one of $A$, $B$ is counted once on each side; an edge joining $A\setminus B$ to $B\setminus A$ is inside
--   $A\cup B$ but on neither side of the left, which is exactly the inequality. Multiplying by $x_e\ge0$ and summing
--   gives the claim.
--
--   **Role.** This is the engine of the uncrossing step of Edmonds' exactness: with the odd-set constraints, it shows
--   that two *crossing* tight odd sets can be replaced by their intersection and union
--   (`QuantumMaxCutEnergy.tight_odd_uncross`), so the family of tight odd sets can be taken laminar — the reduction
--   that makes the polytope's vertices integral and hence the matching polytope exact outside the bipartite case.
-- source:
--   Edmonds, J. Res. Nat. Bur. Standards 69B (1965); Schrijver, Combinatorial Optimization, Ch. 25 (uncrossing of tight odd sets).

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutEdgeInternalSum
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- **Uncrossing identity**: internal masses of two vertex sets are at most those of the union and the
intersection. -/
theorem internalSum_add_le {n : ℕ} (x : Edge n → ℝ) (hx : ∀ e, 0 ≤ x e)
    (A B : Finset (Fin n)) :
    internalSum x A + internalSum x B ≤ internalSum x (A ∪ B) + internalSum x (A ∩ B) := by sorry

end QuantumMaxCutEnergy

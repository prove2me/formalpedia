-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_two_mul_internalSum_le_sum_load
-- name    : QuantumMaxCutEnergy.two_mul_internalSum_le_sum_load
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T05:32:51.305034+00:00
-- url     : https://prove2.me/theorems/409870dc-2c5a-43ad-ae47-8b761e155a36
-- title:
--   Load mass of a vertex set is at least twice its internal edge mass
-- statement:
--   **The load mass of a vertex set is at least twice its internal edge mass.**
--
--   For a nonnegative edge weight $x$ and a vertex set $S$,
--   $$2\,\mathrm{internalSum}\,x\,S\;\le\;\sum_{v\in S}\mathrm{load}_x(v).$$
--
--   **Proof.** Expanding the loads, the right-hand side counts, for each edge $e$, the number
--   $\#\{v\in S : v\in e\}$ of its endpoints in $S$, times $x_e$. An edge with both endpoints in $S$ contributes
--   twice to the internal mass and twice to the load sum; an edge with exactly one endpoint in $S$ contributes
--   nothing to the internal mass and $x_e$ to the load sum; an edge with no endpoint in $S$ contributes nothing to
--   either. Hence the inequality termwise, after multiplying by $x_e\ge0$ and summing.
--
--   **Role.** Together with the vertex constraints this gives $\mathrm{internalSum}\,x\,S\le|S|/2$ for *every* set
--   $S$, odd or even — the bound that the odd-set constraints sharpen to $(|S|-1)/2$ for odd $S$. This is the
--   non-negativity input that the uncrossing argument needs for the sets on which the odd-set constraint does not
--   apply.
-- source:
--   Edmonds, J. Res. Nat. Bur. Standards 69B (1965); the standard vertex-constraint bound in the matching polytope.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutEdgeInternalSum
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- The load mass of a vertex set is at least twice its internal edge mass. -/
theorem two_mul_internalSum_le_sum_load {n : ℕ} (x : Edge n → ℝ) (hx : ∀ e, 0 ≤ x e)
    (S : Finset (Fin n)) :
    2 * internalSum x S ≤ ∑ v ∈ S, loadAt x v := by sorry

end QuantumMaxCutEnergy

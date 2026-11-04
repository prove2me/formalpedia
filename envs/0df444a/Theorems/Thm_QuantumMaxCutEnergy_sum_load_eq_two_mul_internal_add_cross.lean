-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_sum_load_eq_two_mul_internal_add_cross
-- name    : QuantumMaxCutEnergy.sum_load_eq_two_mul_internal_add_cross
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:30:09.029213+00:00
-- url     : https://prove2.me/theorems/56033ec6-ae29-41ff-99d3-4c968ebb364d
-- title:
--   Double counting: load mass over $S$ is twice the internal mass plus the mass leaving
-- statement:
--   **Double counting: load mass = twice the internal mass plus the mass leaving.**
--
--   For any edge weight $x$ and vertex set $S$,
--   $$2\,\mathrm{internalSum}\,x\,S+\mathrm{crossSum}\,x\,S=\sum_{v\in S}\mathrm{load}_x(v).$$
--   Each edge contributes to the load mass over $S$ one per endpoint in $S$: twice if both endpoints lie in $S$, once
--   if exactly one does, and not at all otherwise — the same counts as on the left.
--
--   **Role.** The identity behind the odd-set structure of Edmonds' matching polytope: instantiated at a *tight* set
--   it turns integer-valued counting into the quantitative statement that a tight set sends at most one unit of mass
--   outside itself.
-- source:
--   Edmonds, J. Res. Nat. Bur. Standards 69B (1965); standard double counting for the odd-set polytope.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutEdgeInternalSum
import Definitions.Def_QuantumMaxCutEdgeCrossSum
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- **Double counting**: the load mass over `S` is twice the internal mass plus the mass leaving `S`. -/
theorem sum_load_eq_two_mul_internal_add_cross {n : ℕ} (x : Edge n → ℝ) (S : Finset (Fin n)) :
    2 * internalSum x S + crossSum x S = ∑ v ∈ S, loadAt x v := by sorry

end QuantumMaxCutEnergy

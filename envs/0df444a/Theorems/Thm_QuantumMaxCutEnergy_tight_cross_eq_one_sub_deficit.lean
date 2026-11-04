-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_tight_cross_eq_one_sub_deficit
-- name    : QuantumMaxCutEnergy.tight_cross_eq_one_sub_deficit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:30:06.770362+00:00
-- url     : https://prove2.me/theorems/45381c65-f45d-49fd-9d9f-c25b3199ec95
-- title:
--   Mass leaving a tight set equals one minus the deficit inside it
-- statement:
--   **The mass leaving a tight set is one minus the deficit inside it.**
--
--   For $S$ tight with all loads at most $1$,
--   $$\mathrm{crossSum}\,x\,S=1-\sum_{v\in S}\bigl(1-\mathrm{load}_x(v)\bigr).$$
--   So the "slack" of the vertex constraints inside a tight odd set and the mass it sends outside add up to exactly
--   $1$ — equality, not just the bound. In particular a tight odd set all of whose vertices are saturated sends
--   exactly one unit of mass outside.
--
--   **Role.** The exact form of the previous node; it is the counting identity a perturbation argument needs when it
--   moves mass across the boundary of a tight odd set.
-- source:
--   Edmonds, J. Res. Nat. Bur. Standards 69B (1965); the deficit form of the tight-odd-set identity.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutEdgeInternalSum
import Definitions.Def_QuantumMaxCutEdgeCrossSum
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- **Exact form**: the mass leaving a tight set is one minus the total deficit inside it. -/
theorem tight_cross_eq_one_sub_deficit {n : ℕ} (x : Edge n → ℝ) (hload : ∀ v, loadAt x v ≤ 1)
    (S : Finset (Fin n)) (htight : internalSum x S = ((S.card : ℝ) - 1) / 2) :
    crossSum x S = 1 - ∑ v ∈ S, (1 - loadAt x v) := by sorry

end QuantumMaxCutEnergy

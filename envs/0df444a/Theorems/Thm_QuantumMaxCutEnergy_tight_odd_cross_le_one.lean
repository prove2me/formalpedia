-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_tight_odd_cross_le_one
-- name    : QuantumMaxCutEnergy.tight_odd_cross_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:30:11.412021+00:00
-- url     : https://prove2.me/theorems/6899d749-0459-44dc-bf0e-6c21e1b59be2
-- title:
--   A tight odd set sends at most one unit of edge mass outside itself
-- statement:
--   **A tight odd set sends at most one unit of mass outside itself.**
--
--   If all loads are at most $1$ and $S$ is tight, $\mathrm{internalSum}\,x\,S=(|S|-1)/2$, then
--   $$\mathrm{crossSum}\,x\,S\;\le\;1.$$
--
--   **Proof.** By the double-counting identity,
--   $\mathrm{crossSum}\,x\,S=\sum_{v\in S}\mathrm{load}_x(v)-2\cdot\frac{|S|-1}{2}\le|S|-(|S|-1)=1$.
--
--   **Role.** This is what the odd-set constraints contribute beyond the vertex constraints, and it is the quantitative
--   core of the odd-cycle case: on an odd cycle whose vertices are all saturated, each edge leaving the cycle
--   contributes, and the bound forces the alternating pattern on the cycle to consist of $0$s and $1$s.
-- source:
--   Edmonds, J. Res. Nat. Bur. Standards 69B (1965); Schrijver, Combinatorial Optimization, Ch. 25 (structure of tight odd sets).

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutEdgeInternalSum
import Definitions.Def_QuantumMaxCutEdgeCrossSum
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- **A tight odd set sends at most one unit of mass outside itself.** -/
theorem tight_odd_cross_le_one {n : ℕ} (x : Edge n → ℝ) (hload : ∀ v, loadAt x v ≤ 1)
    (S : Finset (Fin n)) (htight : internalSum x S = ((S.card : ℝ) - 1) / 2) :
    crossSum x S ≤ 1 := by sorry

end QuantumMaxCutEnergy

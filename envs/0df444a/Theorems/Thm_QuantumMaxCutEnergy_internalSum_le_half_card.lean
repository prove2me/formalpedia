-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_internalSum_le_half_card
-- name    : QuantumMaxCutEnergy.internalSum_le_half_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T05:32:59.411119+00:00
-- url     : https://prove2.me/theorems/712b3385-4613-454c-986d-a77390cd35bd
-- title:
--   Internal edge mass of a load-feasible set is at most half its size
-- statement:
--   **Internal edge mass of a load-feasible set is at most half its size.**
--
--   If $x\ge0$ has all vertex loads $\mathrm{load}_x(v)\le1$, then for every vertex set $S$,
--   $$\mathrm{internalSum}\,x\,S\;\le\;\frac{|S|}{2}.$$
--
--   **Proof.** By the previous node $2\,\mathrm{internalSum}\,x\,S\le\sum_{v\in S}\mathrm{load}_x(v)\le|S|$.
--
--   **Role.** This is the "even-set" companion of Edmonds' odd-set constraint
--   $\mathrm{internalSum}\,x\,S\le(|S|-1)/2$: for odd $S$ the odd-set constraint is strictly stronger, and for even
--   $S$ this is the best bound available from the vertex constraints alone. It is the ingredient one needs when
--   uncrossing two tight odd sets $A,B$ whose intersection has *even* size, where the odd-set constraint does not
--   apply to $A\cap B$.
-- source:
--   Edmonds, J. Res. Nat. Bur. Standards 69B (1965); the even-set companion of the odd-set constraints.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutEdgeInternalSum
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- A vertex set whose loads are at most `1` carries internal edge mass at most half its size. -/
theorem internalSum_le_half_card {n : ℕ} (x : Edge n → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v, loadAt x v ≤ 1) (S : Finset (Fin n)) :
    internalSum x S ≤ ((S.card : ℝ)) / 2 := by sorry

end QuantumMaxCutEnergy

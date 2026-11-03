-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_loadAt_eq_sum_pairWeight
-- name    : QuantumMaxCutEnergy.loadAt_eq_sum_pairWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T02:17:54.971789+00:00
-- url     : https://prove2.me/theorems/fef0eedc-f8a3-4a32-9538-be82d6fa4e03
-- title:
--   The vertex load is the sum of pair weights over the other endpoint
-- statement:
--   **The vertex load is the sum of the pair weights over the other endpoint.**
--
--   Let $x\ge0$ be a weight on the edges of a graph on $n$ vertices, $x_{\{a,b\}}$ its value on the unordered pair
--   $\{a,b\}$ (`QuantumMaxCutEnergy.pairWeight`), and $\mathrm{load}_x(a)=\sum_{e\ni a}x_e$ the load of a vertex. Then
--   $$\mathrm{load}_x(a)\;=\;\sum_{b}x_{\{a,b\}} .$$
--
--   **Proof.** Reindex the incident edges of $a$ by their *other* endpoint: the map is injective (an incident edge
--   is determined by its other endpoint together with the side of $a$ it lies on) and its image is exactly the set
--   of vertices other than $a$. The remaining term $b=a$ contributes $x_{\{a,a\}}=0$.
--
--   **Role.** This is the row-sum computation for the doubly stochastic padding `QuantumMaxCutEnergy.padWeight`:
--   $\sum_b(\mathrm{padWeight}\,x)_{ab}=(1-\mathrm{load}_x(a))+\mathrm{load}_x(a)=1$, so a point of the fractional
--   matching polytope becomes a doubly stochastic matrix. It is the bookkeeping bridge between the campaign's
--   edge-indexed model `Edge n` and the `Fin n → Fin n` matrices that Birkhoff's theorem acts on.
-- source:
--   Edmonds, J. Res. Nat. Bur. Standards 69B (1965); the row-sum bookkeeping of the doubly stochastic padding of a fractional matching (Birkhoff-von Neumann).

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutMatchingPadding
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

theorem loadAt_eq_sum_pairWeight {n : ℕ} (x : Edge n → ℝ) (a : Fin n) :
    loadAt x a = ∑ b, pairWeight x a b := by sorry

end QuantumMaxCutEnergy

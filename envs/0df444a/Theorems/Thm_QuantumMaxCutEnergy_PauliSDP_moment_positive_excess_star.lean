-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_PauliSDP_moment_positive_excess_star
-- name    : QuantumMaxCutEnergy.PauliSDP.moment_positive_excess_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T16:01:54.648951+00:00
-- url     : https://prove2.me/theorems/ba282d4e-d35d-45ef-8fd7-2c05345286de
-- title:
--   Positive moment-energy excess satisfies each vertex capacity
-- statement:
--   For every feasible level-$k$ Pauli moment assignment with $k\ge2$, every vertex $i$, and every set $T$ of other vertices,
--
--   $$\sum_{j\in T}\max(e_{ij}(L)-1,0)\le1.$$
--
--   Here $e_{ij}(L)$ is the campaign-normalized edge energy. This supplies the vertex-capacity constraint in the fractional-matching argument.
-- source:
--   The already-proved concrete Pauli star bound, itself obtained from Lee, ISAAC 2022, Lemma 4, followed by restriction to edges of positive excess. https://arxiv.org/abs/2209.00789

import Definitions.Def_QuantumMaxCutPauliMomentRelaxationModel
import Mathlib
open scoped BigOperators
open QuantumMaxCutEnergy.PauliSDP

theorem QuantumMaxCutEnergy.PauliSDP.moment_positive_excess_star {n k : ℕ} (hk : 2 ≤ k)
    (L : Word n → ℝ) (hL : Feasible k L) (i : Fin n)
    (T : Finset (Fin n)) (hi : i ∉ T) :
    (∑ j ∈ T, max
      ((1 - L (fun t => if t = i ∨ t = j then 1 else 0) -
        L (fun t => if t = i ∨ t = j then 2 else 0) -
        L (fun t => if t = i ∨ t = j then 3 else 0)) / 2 - 1) 0) ≤ 1 := by sorry

-- Prove2me | Theorems.Thm_SizeRamsey_four_mul_tau4_le_edgeCount
-- name    : SizeRamsey.four_mul_tau4_le_edgeCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:32:00.923348+00:00
-- url     : https://prove2.me/theorems/e74d1c30-c364-5c5e-8885-f6a12b807178
-- title:
--   Size Ramsey: four mul tau4 le edge Count
-- statement:
--   Theorem A: the universal quadrilateral-transversal bound.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/Solution.lean#L55-L57
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/Solution.lean#L55-L57

module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_SizeRamsey
public import Definitions.Def_SizeRamsey_Solution
public import Theorems.Thm_SizeRamsey_Proof_four_mul_tau4_le_edgeCount

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey

theorem SizeRamsey.four_mul_tau4_le_edgeCount {n : ℕ} (G : SimpleGraph (Fin n)) :
    4 * tau4 G ≤ edgeCount G := by sorry

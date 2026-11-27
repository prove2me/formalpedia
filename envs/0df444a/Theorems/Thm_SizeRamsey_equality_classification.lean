-- Prove2me | Theorems.Thm_SizeRamsey_equality_classification
-- name    : SizeRamsey.equality_classification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:39:28.662557+00:00
-- url     : https://prove2.me/theorems/56a47c11-8952-481e-8bd5-91d1bc42ac19
-- title:
--   Size Ramsey: equality classification
-- statement:
--   Theorem B: all connected equality cases through sixteen edges.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/Solution.lean#L60-L65
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/Solution.lean#L60-L65

module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_SizeRamsey
public import Definitions.Def_SizeRamsey_Solution
public import Theorems.Thm_SizeRamsey_Proof_equality_classification

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey

theorem SizeRamsey.equality_classification {n : ℕ} (G : SimpleGraph (Fin n))
    (hconn : G.Connected) (hpos : 0 < edgeCount G) (hle : edgeCount G ≤ 16) :
    4 * tau4 G = edgeCount G ↔
      Nonempty (G ≃g SimpleGraph.cycleGraph 4) ∨ Nonempty (G ≃g wheel5) ∨
      Nonempty (G ≃g k33MinusEdge) ∨ Nonempty (G ≃g octahedron) := by sorry

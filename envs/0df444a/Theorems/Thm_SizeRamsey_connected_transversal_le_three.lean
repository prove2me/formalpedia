-- Prove2me | Theorems.Thm_SizeRamsey_connected_transversal_le_three
-- name    : SizeRamsey.connected_transversal_le_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:40:27.792869+00:00
-- url     : https://prove2.me/theorems/3238860b-f2fe-4f0e-91ac-dd65e1b79f02
-- title:
--   Size Ramsey: connected transversal le three
-- statement:
--   Corollary C (transversal half): every small connected host has a quadrilateral-transversal of
--   at most three vertices.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/Solution.lean#L69-L72
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/Solution.lean#L69-L72

module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_SizeRamsey
public import Definitions.Def_SizeRamsey_Solution
public import Theorems.Thm_SizeRamsey_Proof_connected_transversal_le_three

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey

theorem SizeRamsey.connected_transversal_le_three {n : ℕ} (G : SimpleGraph (Fin n))
    (hconn : G.Connected) (hle : edgeCount G ≤ 16) :
    ∃ S : Finset (Fin n), c4Transversal G S ∧ S.card ≤ 3 := by sorry

-- Prove2me | Theorems.Thm_SizeRamsey_avoiding_coloring_le_sixteen
-- name    : SizeRamsey.avoiding_coloring_le_sixteen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:41:26.787431+00:00
-- url     : https://prove2.me/theorems/b1637b8c-3180-4902-92c5-349f58432e11
-- title:
--   Size Ramsey: avoiding coloring le sixteen
-- statement:
--   Corollary C (colouring half): an avoiding colouring for every small connected host.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/Solution.lean#L75-L78
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/Solution.lean#L75-L78

module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_SizeRamsey
public import Definitions.Def_SizeRamsey_Solution
public import Theorems.Thm_SizeRamsey_Proof_avoiding_coloring_le_sixteen

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey

theorem SizeRamsey.avoiding_coloring_le_sixteen {n : ℕ} (F : SimpleGraph (Fin n))
    (hconn : F.Connected) (hle : edgeCount F ≤ 16) :
    ∃ R : SimpleGraph (Fin n), R ≤ F ∧ ¬ HasMatching4 R ∧ ¬ HasC4 (F \ R) := by sorry

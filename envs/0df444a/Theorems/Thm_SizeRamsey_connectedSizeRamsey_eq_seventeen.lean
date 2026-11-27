-- Prove2me | Theorems.Thm_SizeRamsey_connectedSizeRamsey_eq_seventeen
-- name    : SizeRamsey.connectedSizeRamsey_eq_seventeen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:32:00.863971+00:00
-- url     : https://prove2.me/theorems/e11c5a7b-7351-5616-b6ed-a49bc09ffc8e
-- title:
--   Size Ramsey: connected Size Ramsey eq seventeen
-- statement:
--   The Size Ramsey construction uses the connected Size Ramsey eq seventeen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/Solution.lean#L84-L95
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/Solution.lean#L84-L95

module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_SizeRamsey
public import Definitions.Def_SizeRamsey_Solution
set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey

theorem SizeRamsey.connectedSizeRamsey_eq_seventeen : connectedSizeRamsey = 17 := by sorry

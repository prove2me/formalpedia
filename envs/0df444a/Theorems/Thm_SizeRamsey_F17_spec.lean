-- Prove2me | Theorems.Thm_SizeRamsey_F17_spec
-- name    : SizeRamsey.F17_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:32:43.436235+00:00
-- url     : https://prove2.me/theorems/2a562ac1-09b4-490d-a02e-1894fa911bc8
-- title:
--   Size Ramsey: F17 spec
-- statement:
--   Theorem D: the explicit seventeen-edge upper witness.
--
--   Source: https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/Solution.lean#L81-L82
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/Solution.lean#L81-L82

module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_SizeRamsey
public import Definitions.Def_SizeRamsey_Solution
public import Theorems.Thm_SizeRamsey_Proof_F17_spec

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey

theorem SizeRamsey.F17_spec : F17.Connected ∧ edgeCount F17 = 17 ∧ ArrowsMatching4C4 F17 := by sorry

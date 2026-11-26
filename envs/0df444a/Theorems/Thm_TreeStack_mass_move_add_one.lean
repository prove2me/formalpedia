-- Prove2me | Theorems.Thm_TreeStack_mass_move_add_one
-- name    : TreeStack.mass_move_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:06:27.567104+00:00
-- url     : https://prove2.me/theorems/2c8f5332-9514-5ec4-a363-f292bb5fbf15
-- title:
--   Tree Stack: mass move add one
-- statement:
--   A legal move lowers total mass by exactly one.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/PebblingMove.lean#L44-L57
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/PebblingMove.lean#L44-L57

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_PebblingMove
set_option autoImplicit false
open TreeStack

theorem TreeStack.mass_move_add_one {V : Type*} [Fintype V] [DecidableEq V]
    (C : Configuration V) {u v : V} (huv : u ≠ v) (hu : 2 ≤ C u) :
    mass (move C u v) + 1 = mass C := by sorry

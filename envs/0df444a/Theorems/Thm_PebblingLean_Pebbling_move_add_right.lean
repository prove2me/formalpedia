-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_move_add_right
-- name    : PebblingLean.Pebbling.move_add_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:39.268628+00:00
-- url     : https://prove2.me/theorems/dcfab2bd-0493-4537-a1a3-b151c7103b29
-- title:
--   Pebbling: move add right
-- statement:
--   Moving from `D` to `E` can be done with an untouched extra distribution
--   added everywhere.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L235-L260
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L235-L260

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_PebblingLean_Delivery
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}

theorem PebblingLean.Pebbling.move_add_right [DecidableEq V] {G : Graph V} {D E A : Pebbling V}
    (hmove : Move G D E) :
    Move G (D + A) (E + A) := by sorry

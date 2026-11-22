-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_reaches_add_right
-- name    : PebblingLean.Pebbling.reaches_add_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:39.40974+00:00
-- url     : https://prove2.me/theorems/05fc87f2-fe9c-4ac8-9795-d12944d602ee
-- title:
--   Pebbling: reaches add right
-- statement:
--   A whole pebbling sequence can be replayed with an untouched extra
--   distribution added everywhere.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L264-L271
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L264-L271

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

theorem PebblingLean.Pebbling.reaches_add_right [DecidableEq V] {G : Graph V} {D E A : Pebbling V}
    (hreach : Reaches G D E) :
    Reaches G (D + A) (E + A) := by sorry

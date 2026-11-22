-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_twoPoint_edge_move
-- name    : PebblingLean.Pebbling.twoPoint_edge_move
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:31.403277+00:00
-- url     : https://prove2.me/theorems/0370f9ff-c66d-4ead-a197-aee3f8a3c66a
-- title:
--   Pebbling: two Point edge move
-- statement:
--   One edge move transfers one pebble from the left support vertex to the
--   right support vertex, consuming two pebbles on the left.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L150-L168
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L150-L168

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

theorem PebblingLean.Pebbling.twoPoint_edge_move [DecidableEq V] {G : Graph V} {u v : V}
    (huv_adj : G.Adj u v) (k a : ℕ) :
    Move G (twoPoint u v (2 * (k + 1)) a) (twoPoint u v (2 * k) (a + 1)) := by sorry

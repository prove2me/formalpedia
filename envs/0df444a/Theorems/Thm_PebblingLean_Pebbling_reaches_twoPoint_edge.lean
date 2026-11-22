-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_reaches_twoPoint_edge
-- name    : PebblingLean.Pebbling.reaches_twoPoint_edge
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:48:32.82415+00:00
-- url     : https://prove2.me/theorems/32309a5a-c0c6-494b-a325-fe763cc872e9
-- title:
--   Pebbling: reaches two Point edge
-- statement:
--   Repeating the same edge move sends `k` pebbles across an edge from a pile
--   of size `2*k`, preserving any accumulator already present at the destination.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L172-L183
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L172-L183

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

theorem PebblingLean.Pebbling.reaches_twoPoint_edge [DecidableEq V] {G : Graph V} {u v : V}
    (huv_adj : G.Adj u v) (k a : ℕ) :
    Reaches G (twoPoint u v (2 * k) a) (twoPoint u v 0 (a + k)) := by sorry

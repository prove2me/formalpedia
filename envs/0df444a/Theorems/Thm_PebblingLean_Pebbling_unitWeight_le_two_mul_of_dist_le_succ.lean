-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_unitWeight_le_two_mul_of_dist_le_succ
-- name    : PebblingLean.Pebbling.unitWeight_le_two_mul_of_dist_le_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:09.265347+00:00
-- url     : https://prove2.me/theorems/54fc0283-d13f-497b-9609-eb116b0d477d
-- title:
--   Pebbling: unit Weight le two mul of dist le succ
-- statement:
--   If moving from `u` to `v` moves at most one step closer to the target, then
--   the new pebble at `v` contributes no more weight than the two pebbles removed
--   from `u`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Weight.lean#L120-L131
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Weight.lean#L120-L131

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_PebblingLean_Weight
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}

theorem PebblingLean.Pebbling.unitWeight_le_two_mul_of_dist_le_succ (dist : V → V → ℕ) {u v target : V}
    (h : dist u target ≤ dist v target + 1) :
    unitWeight dist target v ≤ 2 * unitWeight dist target u := by sorry

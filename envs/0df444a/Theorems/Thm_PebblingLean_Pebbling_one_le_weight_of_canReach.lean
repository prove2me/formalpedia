-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_one_le_weight_of_canReach
-- name    : PebblingLean.Pebbling.one_le_weight_of_canReach
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:46:40.896271+00:00
-- url     : https://prove2.me/theorems/4ad78e41-1bca-4e90-bd25-49f3b1cdfdfb
-- title:
--   Pebbling: one le weight of can Reach
-- statement:
--   If a reachable distribution has a pebble on the target, then its target
--   weight is at least one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Weight.lean#L174-L197
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Weight.lean#L174-L197

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

theorem PebblingLean.Pebbling.one_le_weight_of_canReach [Fintype V] [DecidableEq V] (G : Graph V)
    (dist : V → V → ℕ) {D : Pebbling V} {target : V}
    (hcan : CanReach G D target)
    (hdist_self : dist target target = 0)
    (hdist_edge : ∀ {u v : V}, G.Adj u v → dist u target ≤ dist v target + 1) :
    1 ≤ weight dist D target := by sorry

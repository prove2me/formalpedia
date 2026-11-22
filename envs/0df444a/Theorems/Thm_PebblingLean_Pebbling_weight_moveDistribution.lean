-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_weight_moveDistribution
-- name    : PebblingLean.Pebbling.weight_moveDistribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:11.710948+00:00
-- url     : https://prove2.me/theorems/2c83b25d-8a13-48b1-91a6-46289b7b7b78
-- title:
--   Pebbling: weight move Distribution
-- statement:
--   Exact change in target weight under one legal move.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Weight.lean#L110-L115
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Weight.lean#L110-L115

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

theorem PebblingLean.Pebbling.weight_moveDistribution [Fintype V] [DecidableEq V] (dist : V → V → ℕ)
    (D : Pebbling V) {u v target : V} (huv : u ≠ v) (hD : 2 ≤ D u) :
    weight dist (moveDistribution D u v) target
      = weight dist D target - 2 * unitWeight dist target u + unitWeight dist target v := by sorry

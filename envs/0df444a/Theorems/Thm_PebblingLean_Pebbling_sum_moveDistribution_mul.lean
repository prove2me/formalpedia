-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_sum_moveDistribution_mul
-- name    : PebblingLean.Pebbling.sum_moveDistribution_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:06.026495+00:00
-- url     : https://prove2.me/theorems/f67c832c-7e44-47ed-a40b-9f610334ff35
-- title:
--   Pebbling: sum move Distribution mul
-- statement:
--   Algebraic effect of one legal move on a weighted sum.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Weight.lean#L53-L107
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Weight.lean#L53-L107

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

theorem PebblingLean.Pebbling.sum_moveDistribution_mul [Fintype V] [DecidableEq V] (D : Pebbling V)
    (w : V → ℚ) {u v : V} (huv : u ≠ v) (hD : 2 ≤ D u) :
    (∑ x, ((moveDistribution D u v x : ℕ) : ℚ) * w x)
      = (∑ x, (D x : ℚ) * w x) - 2 * w u + w v := by sorry

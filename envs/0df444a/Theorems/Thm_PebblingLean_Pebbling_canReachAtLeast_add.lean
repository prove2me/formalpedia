-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_canReachAtLeast_add
-- name    : PebblingLean.Pebbling.canReachAtLeast_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:48:41.381681+00:00
-- url     : https://prove2.me/theorems/3c58540e-3b00-4bbf-a1e9-187ef65f6e53
-- title:
--   Pebbling: can Reach At Least add
-- statement:
--   If two distributions can independently deliver `T₁` and `T₂` pebbles to
--   the same target, their sum can deliver `T₁ + T₂`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L275-L295
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L275-L295

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

theorem PebblingLean.Pebbling.canReachAtLeast_add [DecidableEq V] {G : Graph V} {D₁ D₂ : Pebbling V}
    {target : V} {T₁ T₂ : ℕ}
    (h₁ : CanReachAtLeast G D₁ target T₁)
    (h₂ : CanReachAtLeast G D₂ target T₂) :
    CanReachAtLeast G (D₁ + D₂) target (T₁ + T₂) := by sorry

-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_weight_reaches_le_of_dist
-- name    : PebblingLean.Pebbling.weight_reaches_le_of_dist
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:48:11.155648+00:00
-- url     : https://prove2.me/theorems/f92bf0da-e2e6-47b7-a0c9-ad5efe8309f5
-- title:
--   Pebbling: weight reaches le of dist
-- statement:
--   A sequence of legal moves cannot increase target weight.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Weight.lean#L160-L170
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Weight.lean#L160-L170

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

theorem PebblingLean.Pebbling.weight_reaches_le_of_dist [Fintype V] [DecidableEq V] (G : Graph V)
    (dist : V → V → ℕ) {D E : Pebbling V} {target : V}
    (hreach : Reaches G D E)
    (hdist : ∀ {u v : V}, G.Adj u v → dist u target ≤ dist v target + 1) :
    weight dist E target ≤ weight dist D target := by sorry

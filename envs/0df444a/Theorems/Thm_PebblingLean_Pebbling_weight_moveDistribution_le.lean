-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_weight_moveDistribution_le
-- name    : PebblingLean.Pebbling.weight_moveDistribution_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:07.580011+00:00
-- url     : https://prove2.me/theorems/7e7b5486-63d8-44a8-878a-5eebfa05eb0e
-- title:
--   Pebbling: weight move Distribution le
-- statement:
--   A single legal move cannot increase target weight, provided the supplied
--   distance function changes by at most one along graph edges.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Weight.lean#L135-L143
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Weight.lean#L135-L143

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

theorem PebblingLean.Pebbling.weight_moveDistribution_le [Fintype V] [DecidableEq V] (dist : V → V → ℕ)
    (D : Pebbling V) {u v target : V} (huv : u ≠ v) (hD : 2 ≤ D u)
    (hdist : dist u target ≤ dist v target + 1) :
    weight dist (moveDistribution D u v) target ≤ weight dist D target := by sorry

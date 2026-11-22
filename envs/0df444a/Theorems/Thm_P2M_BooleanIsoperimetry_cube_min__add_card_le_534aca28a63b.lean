-- Prove2me | Theorems.Thm_P2M_BooleanIsoperimetry_cube_min__add_card_le_534aca28a63b
-- name    : P2M_BooleanIsoperimetry_cube_min__add_card_le_534aca28a63b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:23:05.06927+00:00
-- url     : https://prove2.me/theorems/0c27893a-711a-4b29-843c-602fe43999da
-- title:
--   P2 M Boolean Isoperimetry cube min  add card le 534aca28a63b: P2 M Boolean Isoperimetry cube min  add card le 534aca28a63b
-- statement:
--   A nonempty vertex of the `n`-cube satisfies `min' + card ≤ n`: its `card`
--   active coordinates all lie in `[min', n)`, an interval of size `n - min'`.  A
--   pure `Finset.min'` bound, used for the per-layer increment upper bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L244-L250
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Macaulay.lean#L244-L250

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry

theorem P2M_BooleanIsoperimetry_cube_min__add_card_le_534aca28a63b {n : ℕ} (w : Cube n) (h : w.Nonempty) :
    (w.min' h : ℕ) + w.card ≤ n := by sorry

alias «BooleanIsoperimetry».«cube_min'_add_card_le» := P2M_BooleanIsoperimetry_cube_min__add_card_le_534aca28a63b

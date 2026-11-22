-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_ne
-- name    : PebblingLean.Pebbling.twoPoint_apply_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:16.686298+00:00
-- url     : https://prove2.me/theorems/4a84ddc5-99d4-46fb-86a3-4cb097aa758b
-- title:
--   Pebbling: two Point apply ne
-- statement:
--   The Pebbling construction uses the two Point apply ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L119-L122
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L119-L122

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

theorem PebblingLean.Pebbling.twoPoint_apply_ne [DecidableEq V] {u v x : V} (ku kv : ℕ)
    (hxu : x ≠ u) (hxv : x ≠ v) :
    twoPoint u v ku kv x = 0 := by sorry

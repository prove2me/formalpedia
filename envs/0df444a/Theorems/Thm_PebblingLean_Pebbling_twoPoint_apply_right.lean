-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_right
-- name    : PebblingLean.Pebbling.twoPoint_apply_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:02.755047+00:00
-- url     : https://prove2.me/theorems/a2b5e6da-ff6c-4637-9665-6a214c1b78c1
-- title:
--   Pebbling: two Point apply right
-- statement:
--   The Pebbling construction uses the two Point apply right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L114-L116
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L114-L116

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

theorem PebblingLean.Pebbling.twoPoint_apply_right [DecidableEq V] {u v : V} (ku kv : ℕ) (hvu : v ≠ u) :
    twoPoint u v ku kv v = kv := by sorry

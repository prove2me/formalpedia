-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_twoPoint_apply_left
-- name    : PebblingLean.Pebbling.twoPoint_apply_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:00.03268+00:00
-- url     : https://prove2.me/theorems/0fd3398d-2deb-49b4-b13b-5b563b9e3822
-- title:
--   Pebbling: two Point apply left
-- statement:
--   The Pebbling construction uses the two Point apply left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L109-L111
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L109-L111

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

theorem PebblingLean.Pebbling.twoPoint_apply_left [DecidableEq V] (u v : V) (ku kv : ℕ) :
    twoPoint u v ku kv u = ku := by sorry

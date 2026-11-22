-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_size_zero
-- name    : PebblingLean.Pebbling.size_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:11.630346+00:00
-- url     : https://prove2.me/theorems/a63a6177-311f-4c45-9386-22d179468212
-- title:
--   Pebbling: size zero
-- statement:
--   The Pebbling construction uses the size zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L62-L63
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L62-L63

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_PebblingLean_Basic
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}

theorem PebblingLean.Pebbling.size_zero [Fintype V] : size (fun _ : V => 0) = 0 := by sorry

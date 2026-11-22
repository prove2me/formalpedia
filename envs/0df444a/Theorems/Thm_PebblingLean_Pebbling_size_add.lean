-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_size_add
-- name    : PebblingLean.Pebbling.size_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:43.063388+00:00
-- url     : https://prove2.me/theorems/a35020b4-07fb-4f2a-9047-052a2dd4b723
-- title:
--   Pebbling: size add
-- statement:
--   The size of a sum of two finite distributions is the sum of their sizes.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L269-L272
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L269-L272

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

theorem PebblingLean.Pebbling.size_add [Fintype V] (D E : Pebbling V) :
    size (D + E) = size D + size E := by sorry

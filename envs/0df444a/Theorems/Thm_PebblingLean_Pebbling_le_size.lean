-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_le_size
-- name    : PebblingLean.Pebbling.le_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:25.283221+00:00
-- url     : https://prove2.me/theorems/7924d7f2-7374-49e9-8825-3db4b2207e34
-- title:
--   Pebbling: le size
-- statement:
--   A single vertex count is bounded by the total size of a finite
--   distribution.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L67-L71
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L67-L71

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

theorem PebblingLean.Pebbling.le_size [Fintype V] (D : Pebbling V) (v : V) :
    D v ≤ size D := by sorry

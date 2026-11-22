-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_supportSize_mul_le_size_of_minOccupiedPileSize
-- name    : PebblingLean.Pebbling.supportSize_mul_le_size_of_minOccupiedPileSize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:42.739612+00:00
-- url     : https://prove2.me/theorems/b08e56d0-7083-4e07-91c5-d59c91f9a273
-- title:
--   Pebbling: support Size mul le size of min Occupied Pile Size
-- statement:
--   If each occupied pile has at least `S` pebbles, then the number of occupied
--   vertices times `S` is at most the total size.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L288-L299
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L288-L299

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

theorem PebblingLean.Pebbling.supportSize_mul_le_size_of_minOccupiedPileSize [Fintype V]
    {D : Pebbling V} {S : ℕ} (hmin : MinOccupiedPileSize D S) :
    supportSize D * S ≤ size D := by sorry

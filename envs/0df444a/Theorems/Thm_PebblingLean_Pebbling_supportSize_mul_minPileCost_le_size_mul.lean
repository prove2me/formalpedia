-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_supportSize_mul_minPileCost_le_size_mul
-- name    : PebblingLean.Pebbling.supportSize_mul_minPileCost_le_size_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:24.411797+00:00
-- url     : https://prove2.me/theorems/d373dd80-2fd7-4602-98c9-51c5751341d5
-- title:
--   Pebbling: support Size mul min Pile Cost le size mul
-- statement:
--   Multiplicative form of the occupied-pile count bound, used in product
--   recurrences.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L303-L308
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L303-L308

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

theorem PebblingLean.Pebbling.supportSize_mul_minPileCost_le_size_mul [Fintype V]
    {D : Pebbling V} {S K : ℕ} (hmin : MinOccupiedPileSize D S) :
    supportSize D * (S * K) ≤ size D * K := by sorry

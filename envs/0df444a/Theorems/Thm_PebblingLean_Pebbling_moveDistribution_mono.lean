-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_moveDistribution_mono
-- name    : PebblingLean.Pebbling.moveDistribution_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:27.294992+00:00
-- url     : https://prove2.me/theorems/ce2f4af2-1795-4b19-b5de-16c628d5fc98
-- title:
--   Pebbling: move Distribution mono
-- statement:
--   Performing the same move from a larger distribution gives a larger result.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L98-L109
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L98-L109

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

theorem PebblingLean.Pebbling.moveDistribution_mono [DecidableEq V] {D D' : Pebbling V} {u v : V}
    (huv : u ≠ v) (hdom : Dominates D' D) :
    Dominates (moveDistribution D' u v) (moveDistribution D u v) := by sorry

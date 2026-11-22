-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_hasSolvableAtMostSize_mono_demand
-- name    : PebblingLean.Pebbling.hasSolvableAtMostSize_mono_demand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:26.843468+00:00
-- url     : https://prove2.me/theorems/0d99b715-918b-4cd3-a8c6-76e0b2135f06
-- title:
--   Pebbling: has Solvable At Most Size mono demand
-- statement:
--   A bounded-size construction for a larger demand also works for any smaller
--   demand.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L252-L257
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L252-L257

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

theorem PebblingLean.Pebbling.hasSolvableAtMostSize_mono_demand [Fintype V] [DecidableEq V]
    {G : Graph V} {T T' k : ℕ} (hTT' : T' ≤ T)
    (h : HasSolvableAtMostSize G T k) :
    HasSolvableAtMostSize G T' k := by sorry

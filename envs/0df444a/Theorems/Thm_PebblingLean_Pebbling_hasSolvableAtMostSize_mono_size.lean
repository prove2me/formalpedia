-- Prove2me | Theorems.Thm_PebblingLean_Pebbling_hasSolvableAtMostSize_mono_size
-- name    : PebblingLean.Pebbling.hasSolvableAtMostSize_mono_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:21.318809+00:00
-- url     : https://prove2.me/theorems/a27e3c8a-5f30-430d-9ef3-6485001b2274
-- title:
--   Pebbling: has Solvable At Most Size mono size
-- statement:
--   A construction with size at most `k` is also a construction with any larger
--   size bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L261-L266
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Basic.lean#L261-L266

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

theorem PebblingLean.Pebbling.hasSolvableAtMostSize_mono_size [Fintype V] [DecidableEq V]
    {G : Graph V} {T k k' : ℕ} (hkk' : k ≤ k')
    (h : HasSolvableAtMostSize G T k) :
    HasSolvableAtMostSize G T k' := by sorry

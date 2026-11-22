-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_sum_unitWeight
-- name    : PebblingLean.Hypercube.sum_unitWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:47.568087+00:00
-- url     : https://prove2.me/theorems/05284047-b6ed-4585-9087-875272453074
-- title:
--   Hypercube: sum unit Weight
-- statement:
--   For a fixed hypercube vertex `base`, the sum of one-pebble weights over all
--   targets is `(3/2)^n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/LowerBound.lean#L86-L96
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/LowerBound.lean#L86-L96

module
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
public import Definitions.Def_LeanPool_PebblingLean_Weight
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling

theorem PebblingLean.Hypercube.sum_unitWeight (n : ℕ) (base : HypercubeVertex n) :
    (∑ target : HypercubeVertex n, unitWeight dist target base) = ((3 : ℚ) / 2) ^ n := by sorry

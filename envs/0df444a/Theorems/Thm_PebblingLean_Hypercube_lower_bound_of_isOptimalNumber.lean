-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_lower_bound_of_isOptimalNumber
-- name    : PebblingLean.Hypercube.lower_bound_of_isOptimalNumber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:50:19.536639+00:00
-- url     : https://prove2.me/theorems/80483987-12ad-4e39-a7cd-78a53ac8b25e
-- title:
--   Hypercube: lower bound of is Optimal Number
-- statement:
--   Lower bound for any `k` certified as the optimal pebbling number.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/LowerBound.lean#L154-L157
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/LowerBound.lean#L154-L157

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

theorem PebblingLean.Hypercube.lower_bound_of_isOptimalNumber {n k : ℕ}
    (hopt : IsOptimalNumber (graph n) k) :
    ((4 : ℚ) / 3) ^ n ≤ (k : ℚ) := by sorry

-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_lower_bound_size_of_solvable
-- name    : PebblingLean.Hypercube.lower_bound_size_of_solvable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:50:50.880414+00:00
-- url     : https://prove2.me/theorems/86e85c8c-60bd-4ec6-8152-12b9ef9d0608
-- title:
--   Hypercube: lower bound size of solvable
-- statement:
--   The lower bound in the paper's usual rational form:
--   every solvable distribution on `Q_n` has at least `(4/3)^n` pebbles.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/LowerBound.lean#L130-L143
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/LowerBound.lean#L130-L143

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

theorem PebblingLean.Hypercube.lower_bound_size_of_solvable {n : ℕ} {D : Pebbling (HypercubeVertex n)}
    (hsolv : Solvable (graph n) D) :
    ((4 : ℚ) / 3) ^ n ≤ (size D : ℚ) := by sorry

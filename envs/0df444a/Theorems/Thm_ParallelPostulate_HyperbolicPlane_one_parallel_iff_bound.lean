-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_one_parallel_iff_bound
-- name    : ParallelPostulate.HyperbolicPlane.one_parallel_iff_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:07:17.249226+00:00
-- url     : https://prove2.me/theorems/241ab922-6767-4f6c-8c68-1969092ce3aa
-- title:
--   Hyperbolic Plane: one parallel iff bound
-- statement:
--   **One parallel exactly when the bound is not negative.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1240-L1249
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1240-L1249

module
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_ParallelPostulate_Geometry
set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem ParallelPostulate.HyperbolicPlane.one_parallel_iff_bound {κ : K} {S : Set (K × K)} (hS : IsLine (plane κ) S)
    {P : K × K} (hP : P ∈ plane κ) (hPS : P ∉ S) :
    (∃! M, IsLine (plane κ) M ∧ P ∈ M ∧ M ∩ S = ∅) ↔ 0 ≤ κ := by sorry

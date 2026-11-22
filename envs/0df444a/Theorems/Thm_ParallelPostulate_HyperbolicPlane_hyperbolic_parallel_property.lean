-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_hyperbolic_parallel_property
-- name    : ParallelPostulate.HyperbolicPlane.hyperbolic_parallel_property
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:07:18.024534+00:00
-- url     : https://prove2.me/theorems/7653b157-c02f-4af1-88b7-71e8984ac537
-- title:
--   Hyperbolic Plane: hyperbolic parallel property
-- statement:
--   **The parallels under a negative bound.** Under a negative bound, through a given point
--   that is not on a line there are at least two different lines, and in fact infinitely many,
--   that do not meet the given line.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1199-L1204
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1199-L1204

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

theorem ParallelPostulate.HyperbolicPlane.hyperbolic_parallel_property {κ : K} (hκ : κ < 0) {S : Set (K × K)}
    (hS : IsLine (plane κ) S) {P : K × K} (hP : P ∈ plane κ) (hPS : P ∉ S) :
    (∃ M₁ M₂ : Set (K × K), M₁ ≠ M₂ ∧ (IsLine (plane κ) M₁ ∧ P ∈ M₁ ∧ M₁ ∩ S = ∅) ∧
      (IsLine (plane κ) M₂ ∧ P ∈ M₂ ∧ M₂ ∩ S = ∅)) ∧
    {M : Set (K × K) | IsLine (plane κ) M ∧ P ∈ M ∧ M ∩ S = ∅}.Infinite := by sorry

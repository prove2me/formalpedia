-- Prove2me | Theorems.Thm_ParallelPostulate_Pairs_Dim_points_eq_through
-- name    : ParallelPostulate.Pairs.Dim.points_eq_through
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:04:25.168843+00:00
-- url     : https://prove2.me/theorems/2438601b-3da9-4b0f-8991-788953fe4570
-- title:
--   Dim: points eq through
-- statement:
--   Two different pairs of a dimension give the dimension: it has the pairs of the dimension
--   from the one to the other.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L364-L381
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L364-L381

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
open ParallelPostulate.Pairs
variable {K : Type*} [Field K]

theorem ParallelPostulate.Pairs.Dim.points_eq_through (L : Dim K) {A B : K × K} (hA : A ∈ L.points)
    (hB : B ∈ L.points) (hAB : A ≠ B) : L.points = (Dim.mk A B).points := by sorry

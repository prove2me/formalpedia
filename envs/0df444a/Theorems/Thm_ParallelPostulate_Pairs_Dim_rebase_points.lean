-- Prove2me | Theorems.Thm_ParallelPostulate_Pairs_Dim_rebase_points
-- name    : ParallelPostulate.Pairs.Dim.rebase_points
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:06:07.6284+00:00
-- url     : https://prove2.me/theorems/be8928d0-fbee-4573-88f5-e164a6d693ee
-- title:
--   Dim: rebase points
-- statement:
--   A dimension can be given its zero at any of its points: it keeps its points.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L128-L145
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L128-L145

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
variable {K : Type*} [CommRing K]
open ParallelPostulate.Pairs.Dim

theorem ParallelPostulate.Pairs.Dim.rebase_points (M : Dim K) {P : K × K} (hP : P ∈ M.points) :
    (M.rebase P).points = M.points := by sorry

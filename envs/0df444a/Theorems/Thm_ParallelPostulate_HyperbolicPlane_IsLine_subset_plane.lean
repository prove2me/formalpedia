-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_IsLine_subset_plane
-- name    : ParallelPostulate.HyperbolicPlane.IsLine.subset_plane
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:06:05.897677+00:00
-- url     : https://prove2.me/theorems/bfff9839-8ae9-4909-ae7a-4fb7d5b3479f
-- title:
--   Is Line: subset plane
-- statement:
--   A line of the plane is a set of points of the plane.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1304-L1307
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1304-L1307

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

theorem ParallelPostulate.HyperbolicPlane.IsLine.subset_plane {κ : ℝ} {S : Set (ℝ × ℝ)} (hS : IsLine (plane κ) S) :
    S ⊆ plane κ := by sorry

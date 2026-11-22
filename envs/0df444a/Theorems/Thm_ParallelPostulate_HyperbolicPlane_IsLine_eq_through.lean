-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_IsLine_eq_through
-- name    : ParallelPostulate.HyperbolicPlane.IsLine.eq_through
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:06:39.302628+00:00
-- url     : https://prove2.me/theorems/f8c7852d-3381-415e-b366-771f6873e2df
-- title:
--   Is Line: eq through
-- statement:
--   A line of the plane through two different points of it is what the dimension through them
--   has in the plane.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1311-L1314
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1311-L1314

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

theorem ParallelPostulate.HyperbolicPlane.IsLine.eq_through {κ : ℝ} {S : Set (ℝ × ℝ)} (hS : IsLine (plane κ) S) {D F : ℝ × ℝ}
    (hD : D ∈ S) (hF : F ∈ S) (hDF : D ≠ F) : S = (Dim.mk D F).points ∩ plane κ := by sorry

-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_ne_of_side_ne_zero
-- name    : ParallelPostulate.HyperbolicPlane.ne_of_side_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:06:37.86102+00:00
-- url     : https://prove2.me/theorems/280ffdb8-45e8-4c78-9679-c68468f34b99
-- title:
--   Hyperbolic Plane: ne of side ne zero
-- statement:
--   A pair of the plane off a line has a side that is not 0, and the three points that make
--   the side not 0 are different.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1289-L1301
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1289-L1301

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

theorem ParallelPostulate.HyperbolicPlane.ne_of_side_ne_zero {X Y Z : ℝ × ℝ} (h : (Dim.mk X Y).side Z ≠ 0) :
    X ≠ Y ∧ Z ≠ X ∧ Z ≠ Y := by sorry

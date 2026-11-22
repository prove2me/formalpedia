-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_plane_mono
-- name    : ParallelPostulate.HyperbolicPlane.plane_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:07:00.584153+00:00
-- url     : https://prove2.me/theorems/9a766ade-85d4-4b7f-90ce-24b1ddc5c82f
-- title:
--   Hyperbolic Plane: plane mono
-- statement:
--   A smaller bound gives a smaller plane.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L871-L876
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L871-L876

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

theorem ParallelPostulate.HyperbolicPlane.plane_mono {κ κ' : K} (h : κ ≤ κ') : plane κ ⊆ plane κ' := by sorry

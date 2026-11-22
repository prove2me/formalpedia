-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_quad_pos
-- name    : ParallelPostulate.HyperbolicPlane.quad_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:06:28.53575+00:00
-- url     : https://prove2.me/theorems/d17450e4-f566-4daa-9c41-dbc0da3e7901
-- title:
--   Hyperbolic Plane: quad pos
-- statement:
--   Near its zero a quadratic is positive, if it is positive at its zero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L795-L816
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L795-L816

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

theorem ParallelPostulate.HyperbolicPlane.quad_pos (α β γ : K) (hα : 0 < α) (hγ : 0 ≤ γ) :
    ∃ t : K, 0 < t ∧ 0 < α + β * t - γ * t ^ 2 := by sorry

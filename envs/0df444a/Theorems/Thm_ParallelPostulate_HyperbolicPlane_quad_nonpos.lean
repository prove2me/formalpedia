-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_quad_nonpos
-- name    : ParallelPostulate.HyperbolicPlane.quad_nonpos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:05:27.623173+00:00
-- url     : https://prove2.me/theorems/2cdab0fc-c260-43e4-81dd-09a30bf0ed33
-- title:
--   Hyperbolic Plane: quad nonpos
-- statement:
--   Far enough along, a quadratic that opens downward is not positive.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L819-L837
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L819-L837

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

theorem ParallelPostulate.HyperbolicPlane.quad_nonpos (α β γ : K) (hγ : 0 < γ) :
    ∃ T : K, ∀ t : K, T ≤ t → α + β * t - γ * t ^ 2 ≤ 0 := by sorry

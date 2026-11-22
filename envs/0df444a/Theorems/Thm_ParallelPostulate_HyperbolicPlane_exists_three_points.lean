-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_exists_three_points
-- name    : ParallelPostulate.HyperbolicPlane.exists_three_points
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:06:32.926789+00:00
-- url     : https://prove2.me/theorems/4b08ca07-3635-429b-a3ed-9f4bae2059da
-- title:
--   Hyperbolic Plane: exists three points
-- statement:
--   **There are three points of the plane that are not on one line.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L979-L997
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L979-L997

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

theorem ParallelPostulate.HyperbolicPlane.exists_three_points (κ : K) :
    ∃ A B C : K × K, A ∈ plane κ ∧ B ∈ plane κ ∧ C ∈ plane κ ∧
      ∀ S, IsLine (plane κ) S → ¬ (A ∈ S ∧ B ∈ S ∧ C ∈ S) := by sorry

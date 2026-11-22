-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_crosses
-- name    : ParallelPostulate.HyperbolicPlane.crosses
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:05:26.264677+00:00
-- url     : https://prove2.me/theorems/8e17af29-4f76-4312-99ef-c6dc3913f2ac
-- title:
--   Hyperbolic Plane: crosses
-- statement:
--   Two points of the plane on opposite sides of a dimension: between them the dimension has
--   a point of the plane.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1107-L1136
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1107-L1136

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

theorem ParallelPostulate.HyperbolicPlane.crosses (κ : K) (M : Dim K) (hM : M.zero ≠ M.one) {P Q : K × K} (hP : P ∈ plane κ)
    (hQ : Q ∈ plane κ) (h : M.side P * M.side Q < 0) :
    ∃ Y : K × K, Y ∈ M.points ∧ Y ∈ plane κ ∧ Between P Y Q := by sorry

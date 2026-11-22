-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_between_trichotomy
-- name    : ParallelPostulate.HyperbolicPlane.between_trichotomy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:06:36.758448+00:00
-- url     : https://prove2.me/theorems/74888669-91de-420a-bd42-6b52757bf321
-- title:
--   Hyperbolic Plane: between trichotomy
-- statement:
--   **Of three different points on a line, one is between the two others.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1256-L1285
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1256-L1285

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

theorem ParallelPostulate.HyperbolicPlane.between_trichotomy {A B C : ℝ × ℝ} (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C)
    (hB : B ∈ (Dim.mk A C).points) : Between A B C ∨ Between B A C ∨ Between A C B := by sorry

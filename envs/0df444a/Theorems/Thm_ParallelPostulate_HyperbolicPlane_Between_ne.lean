-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_ne
-- name    : ParallelPostulate.HyperbolicPlane.Between.ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:04:25.543075+00:00
-- url     : https://prove2.me/theorems/3f18a872-7c66-4b55-8726-cfa7eebe66f5
-- title:
--   Between: ne
-- statement:
--   If `B` is between `A` and `C`, the three are different.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1026-L1035
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1026-L1035

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

theorem ParallelPostulate.HyperbolicPlane.Between.ne {A B C : K × K} (h : Between A B C) : A ≠ B ∧ B ≠ C ∧ A ≠ C := by sorry

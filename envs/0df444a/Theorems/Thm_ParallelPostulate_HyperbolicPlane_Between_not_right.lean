-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_not_right
-- name    : ParallelPostulate.HyperbolicPlane.Between.not_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:06:33.112766+00:00
-- url     : https://prove2.me/theorems/ce1980d8-6bd5-45df-9eeb-7e70c32a5549
-- title:
--   Between: not right
-- statement:
--   And `C` is not between `A` and `B`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1058-L1074
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1058-L1074

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

theorem ParallelPostulate.HyperbolicPlane.Between.not_right {A B C : K × K} (h : Between A B C) : ¬ Between A C B := by sorry

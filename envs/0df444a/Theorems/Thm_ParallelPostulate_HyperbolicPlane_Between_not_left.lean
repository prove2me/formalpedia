-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_not_left
-- name    : ParallelPostulate.HyperbolicPlane.Between.not_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:06:32.276627+00:00
-- url     : https://prove2.me/theorems/21913efd-9bfd-47d5-abc3-4c51893e5697
-- title:
--   Between: not left
-- statement:
--   **Of three pairs of a dimension, one only is between the other two.** If `B` is between
--   `A` and `C`, then `A` is not between `B` and `C`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1039-L1055
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1039-L1055

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

theorem ParallelPostulate.HyperbolicPlane.Between.not_left {A B C : K × K} (h : Between A B C) : ¬ Between B A C := by sorry

-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_symm
-- name    : ParallelPostulate.HyperbolicPlane.Between.symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:04:20.426252+00:00
-- url     : https://prove2.me/theorems/b22c9080-d21c-4b27-8916-eecd88bee8a7
-- title:
--   Between: symm
-- statement:
--   If `B` is between `A` and `C`, it is between `C` and `A`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1010-L1017
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1010-L1017

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

theorem ParallelPostulate.HyperbolicPlane.Between.symm {A B C : K × K} (h : Between A B C) : Between C B A := by sorry

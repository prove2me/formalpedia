-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_mem
-- name    : ParallelPostulate.HyperbolicPlane.Between.mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:06:32.09372+00:00
-- url     : https://prove2.me/theorems/f60741f4-b960-461f-91ec-2190deb09d99
-- title:
--   Between: mem
-- statement:
--   A pair between `A` and `C` is a pair of the dimension from `A` to `C`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1021-L1023
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1021-L1023

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
omit [IsStrictOrderedRing K]

theorem ParallelPostulate.HyperbolicPlane.Between.mem {A B C : K × K} (h : Between A B C) : B ∈ (Dim.mk A C).points := by sorry

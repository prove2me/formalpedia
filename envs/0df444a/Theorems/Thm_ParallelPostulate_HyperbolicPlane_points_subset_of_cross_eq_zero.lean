-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_points_subset_of_cross_eq_zero
-- name    : ParallelPostulate.HyperbolicPlane.points_subset_of_cross_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:06:12.09695+00:00
-- url     : https://prove2.me/theorems/1d51ac70-ac5f-40e0-918d-75136cdc8bb5
-- title:
--   Hyperbolic Plane: points subset of cross eq zero
-- statement:
--   Let two dimensions pass through one pair, each with a direction that is a multiple of the
--   direction of `L`. Then the pairs of the first are pairs of the second.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L485-L513
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L485-L513

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
variable {K : Type*} [Field K]

theorem ParallelPostulate.HyperbolicPlane.points_subset_of_cross_eq_zero (L M M' : Dim K) (hL : L.zero ≠ L.one)
    (hM' : M'.zero ≠ M'.one) (h : cross L.dir M.dir = 0) (h' : cross L.dir M'.dir = 0)
    {P : K × K} (hP : P ∈ M.points) (hP' : P ∈ M'.points) : M.points ⊆ M'.points := by sorry

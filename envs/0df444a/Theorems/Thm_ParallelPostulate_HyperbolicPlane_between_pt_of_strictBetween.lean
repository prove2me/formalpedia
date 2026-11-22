-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_between_pt_of_strictBetween
-- name    : ParallelPostulate.HyperbolicPlane.between_pt_of_strictBetween
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:06:05.509723+00:00
-- url     : https://prove2.me/theorems/99d4fa4d-2724-4a5a-9597-61d5c9c22cb2
-- title:
--   Hyperbolic Plane: between pt of strict Between
-- statement:
--   **Numbers in order give pairs in order.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1320-L1339
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1320-L1339

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

theorem ParallelPostulate.HyperbolicPlane.between_pt_of_strictBetween (M : Dim ℝ) (hM : M.zero ≠ M.one) {a b c : ℝ}
    (h : StrictBetween a c b) : Between (M.pt a) (M.pt c) (M.pt b) := by sorry

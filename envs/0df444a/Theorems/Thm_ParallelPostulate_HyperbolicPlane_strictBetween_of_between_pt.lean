-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_strictBetween_of_between_pt
-- name    : ParallelPostulate.HyperbolicPlane.strictBetween_of_between_pt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:06:41.858073+00:00
-- url     : https://prove2.me/theorems/132cc87e-93a7-4048-9a0b-3724f688ab91
-- title:
--   Hyperbolic Plane: strict Between of between pt
-- statement:
--   **Pairs in order come from numbers in order.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1342-L1358
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1342-L1358

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

theorem ParallelPostulate.HyperbolicPlane.strictBetween_of_between_pt (M : Dim ℝ) (hM : M.zero ≠ M.one) {a b c : ℝ}
    (h : Between (M.pt a) (M.pt c) (M.pt b)) : StrictBetween a c b := by sorry

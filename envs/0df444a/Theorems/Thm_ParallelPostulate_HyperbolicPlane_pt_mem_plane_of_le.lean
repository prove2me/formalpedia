-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_pt_mem_plane_of_le
-- name    : ParallelPostulate.HyperbolicPlane.pt_mem_plane_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:06:43.989644+00:00
-- url     : https://prove2.me/theorems/70973581-6893-4ece-958c-05a091d5f0f9
-- title:
--   Hyperbolic Plane: pt mem plane of le
-- statement:
--   The numbers of a dimension whose pairs are points of the plane make an interval.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1361-L1376
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L1361-L1376

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

theorem ParallelPostulate.HyperbolicPlane.pt_mem_plane_of_le {κ : ℝ} (M : Dim ℝ) {a b c : ℝ} (ha : M.pt a ∈ plane κ)
    (hb : M.pt b ∈ plane κ) (hac : a ≤ c) (hcb : c ≤ b) : M.pt c ∈ plane κ := by sorry

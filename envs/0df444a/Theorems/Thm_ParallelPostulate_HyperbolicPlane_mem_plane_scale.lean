-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_mem_plane_scale
-- name    : ParallelPostulate.HyperbolicPlane.mem_plane_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:07:06.282753+00:00
-- url     : https://prove2.me/theorems/bb688d7e-a87e-44d3-9ed2-9b8cc3b79dc9
-- title:
--   Hyperbolic Plane: mem plane scale
-- statement:
--   The bound `κ s²` is the bound `κ` with every pair made `s` times as large.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L880-L885
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate/Geometry.lean#L880-L885

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

theorem ParallelPostulate.HyperbolicPlane.mem_plane_scale (κ s : K) (p : K × K) :
    p ∈ plane (κ * s ^ 2) ↔ (s * p.1, s * p.2) ∈ plane κ := by sorry

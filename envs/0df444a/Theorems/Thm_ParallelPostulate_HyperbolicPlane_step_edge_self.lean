-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_step_edge_self
-- name    : ParallelPostulate.HyperbolicPlane.step_edge_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:15:20.803301+00:00
-- url     : https://prove2.me/theorems/ae43d0a6-0ee8-457b-9547-ab6f30b25f93
-- title:
--   Hyperbolic Plane: step edge self
-- statement:
--   **A number on the edge is its own double.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1275-L1279
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1275-L1279

module
public import Definitions.Def_LeanPool_ParallelPostulate_Geometry
public import Definitions.Def_LeanPool_ParallelPostulate_Hilbert
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_LeanPool_ParallelPostulate
set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem ParallelPostulate.HyperbolicPlane.step_edge_self {κ e : K} (he : 1 + κ * e ^ 2 = 0) : step κ e e = e := by sorry

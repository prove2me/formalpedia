-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_step_bound
-- name    : ParallelPostulate.HyperbolicPlane.step_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:13:17.338146+00:00
-- url     : https://prove2.me/theorems/d09df98f-3dee-4472-998f-15c396351422
-- title:
--   Hyperbolic Plane: step bound
-- statement:
--   The bound at a step.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L973-L977
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L973-L977

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
variable {K : Type*} [Field K]

theorem ParallelPostulate.HyperbolicPlane.step_bound {κ t u : K} (h : 1 - κ * t * u ≠ 0) :
    1 + κ * step κ t u ^ 2 = (1 + κ * t ^ 2) * (1 + κ * u ^ 2) / (1 - κ * t * u) ^ 2 := by sorry

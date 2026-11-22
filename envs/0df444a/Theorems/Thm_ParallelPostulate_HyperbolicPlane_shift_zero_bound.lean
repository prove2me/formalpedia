-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_shift_zero_bound
-- name    : ParallelPostulate.HyperbolicPlane.shift_zero_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:14:52.923022+00:00
-- url     : https://prove2.me/theorems/65c6d0bd-1bf8-4792-ad2e-0f8bb5e41a67
-- title:
--   Hyperbolic Plane: shift zero bound
-- statement:
--   With the bound 0 the motion is adding.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L992-L993
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L992-L993

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

theorem ParallelPostulate.HyperbolicPlane.shift_zero_bound (a : K) (p : K × K) : shift 0 a 1 p = (p.1 + a, p.2) := by sorry

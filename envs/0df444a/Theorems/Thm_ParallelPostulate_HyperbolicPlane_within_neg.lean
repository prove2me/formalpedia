-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_within_neg
-- name    : ParallelPostulate.HyperbolicPlane.within_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:15:20.097229+00:00
-- url     : https://prove2.me/theorems/4d3fec20-22d6-4d10-843a-0531fb4bd2fc
-- title:
--   Hyperbolic Plane: within neg
-- statement:
--   The step back of a number within the bound is within the bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1230-L1233
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1230-L1233

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
omit [IsStrictOrderedRing K]

theorem ParallelPostulate.HyperbolicPlane.within_neg {κ t : K} (ht : 0 < 1 + κ * t ^ 2) : 0 < 1 + κ * (-t) ^ 2 := by sorry

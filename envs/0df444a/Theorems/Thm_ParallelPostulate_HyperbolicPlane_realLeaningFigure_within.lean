-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_realLeaningFigure_within
-- name    : ParallelPostulate.HyperbolicPlane.realLeaningFigure_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:13:40.041291+00:00
-- url     : https://prove2.me/theorems/025a5231-d7ba-4316-bd66-f6daaf561d8c
-- title:
--   Hyperbolic Plane: real Leaning Figure within
-- statement:
--   Its zeros and its 1s are points of the plane of the bound `-1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L3772-L3775
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L3772-L3775

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
open Real

theorem ParallelPostulate.HyperbolicPlane.realLeaningFigure_within :
    realLeaningFigure.a.zero ∈ plane (-1 : ℝ) ∧ realLeaningFigure.a.one ∈ plane (-1 : ℝ) ∧
      realLeaningFigure.b.one ∈ plane (-1 : ℝ) ∧ realLeaningFigure.c.one ∈ plane (-1 : ℝ) := by sorry

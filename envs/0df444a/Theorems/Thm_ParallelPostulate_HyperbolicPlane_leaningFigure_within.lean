-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_leaningFigure_within
-- name    : ParallelPostulate.HyperbolicPlane.leaningFigure_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:16:17.224562+00:00
-- url     : https://prove2.me/theorems/e0eb6d88-72a4-473c-8889-a855868bfe34
-- title:
--   Hyperbolic Plane: leaning Figure within
-- statement:
--   Its zeros and its 1s are points of the plane of the bound `-1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L3666-L3669
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L3666-L3669

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

theorem ParallelPostulate.HyperbolicPlane.leaningFigure_within :
    leaningFigure.a.zero ∈ plane (-1 : ℚ) ∧ leaningFigure.a.one ∈ plane (-1 : ℚ) ∧
      leaningFigure.b.one ∈ plane (-1 : ℚ) ∧ leaningFigure.c.one ∈ plane (-1 : ℚ) := by sorry

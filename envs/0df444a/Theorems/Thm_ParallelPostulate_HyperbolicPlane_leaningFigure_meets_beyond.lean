-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_leaningFigure_meets_beyond
-- name    : ParallelPostulate.HyperbolicPlane.leaningFigure_meets_beyond
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:13:37.214422+00:00
-- url     : https://prove2.me/theorems/697af33f-2ba3-4fbf-ba8e-4f2504b380cf
-- title:
--   Hyperbolic Plane: leaning Figure meets beyond
-- statement:
--   As dimensions, `b` and `c` meet at the number 10 of each, at the pair `(0, 5)`, which is
--   not a point of the plane.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L3698-L3704
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L3698-L3704

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

theorem ParallelPostulate.HyperbolicPlane.leaningFigure_meets_beyond :
    leaningFigure.b.pt 10 = (0, 5) ∧ leaningFigure.c.pt 10 = (0, 5) ∧
      ((0 : ℚ), (5 : ℚ)) ∉ plane (-1 : ℚ) := by sorry

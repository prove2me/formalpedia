-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_leaningFigure_values
-- name    : ParallelPostulate.HyperbolicPlane.leaningFigure_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:13:37.544905+00:00
-- url     : https://prove2.me/theorems/06f35755-1b42-40bd-a22f-37757967b1dc
-- title:
--   Hyperbolic Plane: leaning Figure values
-- statement:
--   The sides of `b1` and of `c1`, and the cross product of the directions of `b` and `c`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L3672-L3676
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L3672-L3676

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

theorem ParallelPostulate.HyperbolicPlane.leaningFigure_values :
    leaningFigure.a.side leaningFigure.b.one = 3 / 10 ∧
      leaningFigure.a.side leaningFigure.c.one = 3 / 10 ∧
      cross leaningFigure.b.dir leaningFigure.c.dir = 3 / 100 := by sorry

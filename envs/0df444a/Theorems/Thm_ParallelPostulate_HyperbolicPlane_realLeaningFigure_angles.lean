-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_realLeaningFigure_angles
-- name    : ParallelPostulate.HyperbolicPlane.realLeaningFigure_angles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:13:47.140593+00:00
-- url     : https://prove2.me/theorems/7c2964af-cb22-4c61-b2d3-dfaa2ce80a78
-- title:
--   Hyperbolic Plane: real Leaning Figure angles
-- statement:
--   **The two interior angles are together less than two right angles.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L3821-L3826
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L3821-L3826

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

theorem ParallelPostulate.HyperbolicPlane.realLeaningFigure_angles :
    kleinAngle (-1) realLeaningFigure.a.zero realLeaningFigure.a.one realLeaningFigure.b.one
      + kleinAngle (-1) realLeaningFigure.a.one realLeaningFigure.a.zero realLeaningFigure.c.one
      < π := by sorry

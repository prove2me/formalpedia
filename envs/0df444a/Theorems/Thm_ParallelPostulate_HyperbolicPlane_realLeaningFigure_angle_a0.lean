-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_realLeaningFigure_angle_a0
-- name    : ParallelPostulate.HyperbolicPlane.realLeaningFigure_angle_a0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:13:42.888012+00:00
-- url     : https://prove2.me/theorems/d6e82497-1f56-490a-983c-897c148be840
-- title:
--   Hyperbolic Plane: real Leaning Figure angle a0
-- statement:
--   **The interior angle at `a0` is a right angle.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L3784-L3790
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L3784-L3790

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

theorem ParallelPostulate.HyperbolicPlane.realLeaningFigure_angle_a0 :
    kleinAngle (-1) realLeaningFigure.a.zero realLeaningFigure.a.one realLeaningFigure.b.one
      = π / 2 := by sorry

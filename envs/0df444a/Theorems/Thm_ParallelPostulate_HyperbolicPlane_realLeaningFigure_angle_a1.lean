-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_realLeaningFigure_angle_a1
-- name    : ParallelPostulate.HyperbolicPlane.realLeaningFigure_angle_a1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:13:54.304243+00:00
-- url     : https://prove2.me/theorems/1a4af215-3622-4e5a-968e-8fba9e53b599
-- title:
--   Hyperbolic Plane: real Leaning Figure angle a1
-- statement:
--   **The interior angle at `a1`** is the angle whose cosine is `3 / √409`, about 81.5 degrees.
--   With the angles of Euclid it would be the angle whose cosine is `3 / √634`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L3794-L3811
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L3794-L3811

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

theorem ParallelPostulate.HyperbolicPlane.realLeaningFigure_angle_a1 :
    kleinAngle (-1) realLeaningFigure.a.one realLeaningFigure.a.zero realLeaningFigure.c.one
      = arccos (3 / √409) := by sorry

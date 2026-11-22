-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_realLeaningFigure_never_meets
-- name    : ParallelPostulate.HyperbolicPlane.realLeaningFigure_never_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:13:47.745856+00:00
-- url     : https://prove2.me/theorems/19c12ae5-61a1-4464-a06b-5934c11ce0ce
-- title:
--   Hyperbolic Plane: real Leaning Figure never meets
-- statement:
--   **In the plane of the bound `-1` the lines of `b` and `c` do not meet**, on either side
--   of `a`. As dimensions they meet at the pair `(0, 5)`, which is not a point of the plane.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L3830-L3841
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L3830-L3841

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

theorem ParallelPostulate.HyperbolicPlane.realLeaningFigure_never_meets :
    (realLeaningFigure.b.points ∩ plane (-1 : ℝ)) ∩ (realLeaningFigure.c.points ∩ plane (-1 : ℝ))
      = ∅ := by sorry

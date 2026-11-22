-- Prove2me | Theorems.Thm_ParallelPostulate_Pairs_Figure_reverse_angles
-- name    : ParallelPostulate.Pairs.Figure.reverse_angles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:11:47.544322+00:00
-- url     : https://prove2.me/theorems/aa1efd51-930f-4b0a-8d3c-3264ddd5cc79
-- title:
--   Figure: reverse angles
-- statement:
--   The two interior angles of the figure with `a` run backwards are the two interior angles
--   of the figure, in the other order.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L813-L820
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L813-L820

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
open ParallelPostulate.ThreeDimensions
open Pairs
open Real InnerProductGeometry

theorem ParallelPostulate.Pairs.Figure.reverse_angles (F : Figure ℝ) :
    angle (toE F.reverse.a.dir) (toE F.reverse.b.dir)
        + angle (toE (-F.reverse.a.dir)) (toE F.reverse.c.dir)
      = angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) := by sorry

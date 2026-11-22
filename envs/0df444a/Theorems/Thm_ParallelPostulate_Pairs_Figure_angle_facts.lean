-- Prove2me | Theorems.Thm_ParallelPostulate_Pairs_Figure_angle_facts
-- name    : ParallelPostulate.Pairs.Figure.angle_facts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:11:47.179905+00:00
-- url     : https://prove2.me/theorems/430d0671-964d-43d9-ae15-d89e97c3fab5
-- title:
--   Figure: angle facts
-- statement:
--   What the two interior angles of a figure say, gathered.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L713-L730
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L713-L730

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

theorem ParallelPostulate.Pairs.Figure.angle_facts (F : Figure ℝ)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one) :
    sin (angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir))
        * (‖toE F.b.dir‖ * ‖toE F.c.dir‖) = cross F.b.dir F.c.dir ∧
      0 < ‖toE F.b.dir‖ * ‖toE F.c.dir‖ ∧
      0 < angle (toE F.a.dir) (toE F.b.dir) ∧ angle (toE F.a.dir) (toE F.b.dir) < π ∧
      0 < angle (toE (-F.a.dir)) (toE F.c.dir) ∧ angle (toE (-F.a.dir)) (toE F.c.dir) < π := by sorry

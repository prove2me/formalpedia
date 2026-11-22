-- Prove2me | Theorems.Thm_ParallelPostulate_ThreeDimensions_other_side_either_side
-- name    : ParallelPostulate.ThreeDimensions.other_side_either_side
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:14:41.971492+00:00
-- url     : https://prove2.me/theorems/4c40d8e6-9421-4776-a371-434b9d89413c
-- title:
--   Three Dimensions: other side either side
-- statement:
--   **More than two right angles, on either side: the lines meet on the other side.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L871-L890
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L871-L890

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

theorem ParallelPostulate.ThreeDimensions.other_side_either_side (F : Figure ℝ)
    (hside : 0 < F.a.side F.b.one * F.a.side F.c.one)
    (hang : π < angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir)) :
    ∃ t u : ℝ, t < 0 ∧ u < 0 ∧ F.b.pt t = F.c.pt u ∧
      F.a.side (F.b.pt t) * F.a.side F.b.one < 0 := by sorry

-- Prove2me | Theorems.Thm_ParallelPostulate_ThreeDimensions_cross_neg_of_angles
-- name    : ParallelPostulate.ThreeDimensions.cross_neg_of_angles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:11:58.635846+00:00
-- url     : https://prove2.me/theorems/539e3b3b-9ea5-4cf6-9f33-ab98f02c55cb
-- title:
--   Three Dimensions: cross neg of angles
-- statement:
--   More than two right angles: `c` is a turn to the right of `b`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L750-L760
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L750-L760

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

theorem ParallelPostulate.ThreeDimensions.cross_neg_of_angles (F : Figure ℝ)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one)
    (hang : π < angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir)) :
    cross F.b.dir F.c.dir < 0 := by sorry

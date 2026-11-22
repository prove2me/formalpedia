-- Prove2me | Theorems.Thm_ParallelPostulate_ThreeDimensions_cross_eq_zero_of_angles
-- name    : ParallelPostulate.ThreeDimensions.cross_eq_zero_of_angles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:11:53.833336+00:00
-- url     : https://prove2.me/theorems/8e5222b2-2a3c-49b6-ba97-eda8717b5305
-- title:
--   Three Dimensions: cross eq zero of angles
-- statement:
--   Two right angles: the cross product of the directions of `b` and `c` is zero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L742-L747
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L742-L747

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

theorem ParallelPostulate.ThreeDimensions.cross_eq_zero_of_angles (F : Figure ℝ)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one)
    (hang : angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) = π) :
    cross F.b.dir F.c.dir = 0 := by sorry

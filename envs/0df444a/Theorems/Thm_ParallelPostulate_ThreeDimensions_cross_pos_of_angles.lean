-- Prove2me | Theorems.Thm_ParallelPostulate_ThreeDimensions_cross_pos_of_angles
-- name    : ParallelPostulate.ThreeDimensions.cross_pos_of_angles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:11:56.603087+00:00
-- url     : https://prove2.me/theorems/282d85c1-6669-456c-a1f3-935e88875dd7
-- title:
--   Three Dimensions: cross pos of angles
-- statement:
--   Less than two right angles: `c` is a turn to the left of `b`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L733-L739
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L733-L739

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

theorem ParallelPostulate.ThreeDimensions.cross_pos_of_angles (F : Figure ℝ)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one)
    (hang : angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) < π) :
    0 < cross F.b.dir F.c.dir := by sorry

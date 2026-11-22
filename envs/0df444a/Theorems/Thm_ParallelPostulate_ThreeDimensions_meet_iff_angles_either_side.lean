-- Prove2me | Theorems.Thm_ParallelPostulate_ThreeDimensions_meet_iff_angles_either_side
-- name    : ParallelPostulate.ThreeDimensions.meet_iff_angles_either_side
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:14:53.0355+00:00
-- url     : https://prove2.me/theorems/88f29d4c-18af-4e11-92fd-1915ffb5850b
-- title:
--   Three Dimensions: meet iff angles either side
-- statement:
--   **The postulate and its converse, on either side.** In the real plane, let `b1` and `c1`
--   lie on the same side of `a`. The lines `b` and `c`, produced towards `b1` and `c1`, meet exactly
--   when the two interior angles on that side are together less than two right angles.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L895-L912
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L895-L912

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

theorem ParallelPostulate.ThreeDimensions.meet_iff_angles_either_side (F : Figure ℝ)
    (hside : 0 < F.a.side F.b.one * F.a.side F.c.one) :
    (∃ t u : ℝ, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u) ↔
      angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) < π := by sorry

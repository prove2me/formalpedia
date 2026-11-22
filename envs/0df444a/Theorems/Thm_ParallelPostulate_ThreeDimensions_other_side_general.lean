-- Prove2me | Theorems.Thm_ParallelPostulate_ThreeDimensions_other_side_general
-- name    : ParallelPostulate.ThreeDimensions.other_side_general
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:12:53.762186+00:00
-- url     : https://prove2.me/theorems/20431946-4643-454d-ad0d-9cbc060367c1
-- title:
--   Three Dimensions: other side general
-- statement:
--   **More than two right angles, with `b1` and `c1` on the left of `a`, for any figure in the
--   real plane: the lines meet on the right of `a`.** For either side see
--   `other_side_either_side`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L783-L787
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L783-L787

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

theorem ParallelPostulate.ThreeDimensions.other_side_general (F : Figure ℝ)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one)
    (hang : π < angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir)) :
    ∃ t u : ℝ, t < 0 ∧ u < 0 ∧ F.b.pt t = F.c.pt u ∧ F.a.side (F.b.pt t) < 0 := by sorry

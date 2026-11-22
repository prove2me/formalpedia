-- Prove2me | Theorems.Thm_ParallelPostulate_ThreeDimensions_meet_on_side_iff_angles
-- name    : ParallelPostulate.ThreeDimensions.meet_on_side_iff_angles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:13:05.853186+00:00
-- url     : https://prove2.me/theorems/acbe02e3-0c0f-4353-8003-45f7255e4728
-- title:
--   Three Dimensions: meet on side iff angles
-- statement:
--   **The postulate and its converse.** In the real plane, the lines `b` and `c` meet on the
--   side of `b1` and `c1` exactly when the two interior angles on that side are together less than
--   two right angles.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L792-L807
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L792-L807

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

theorem ParallelPostulate.ThreeDimensions.meet_on_side_iff_angles (F : Figure ℝ)
    (hb : 0 < F.a.side F.b.one) (hc : 0 < F.a.side F.c.one) :
    (∃ t u : ℝ, 0 < t ∧ 0 < u ∧ F.b.pt t = F.c.pt u) ↔
      angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) < π := by sorry

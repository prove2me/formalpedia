-- Prove2me | Theorems.Thm_ParallelPostulate_ThreeDimensions_never_meet_either_side
-- name    : ParallelPostulate.ThreeDimensions.never_meet_either_side
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:14:47.865438+00:00
-- url     : https://prove2.me/theorems/a41f0acb-19fd-4f33-9d7e-d7c2f22e43f9
-- title:
--   Three Dimensions: never meet either side
-- statement:
--   **Two right angles, on either side: the lines never meet.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L855-L868
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L855-L868

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

theorem ParallelPostulate.ThreeDimensions.never_meet_either_side (F : Figure ℝ)
    (hside : 0 < F.a.side F.b.one * F.a.side F.c.one)
    (hang : angle (toE F.a.dir) (toE F.b.dir) + angle (toE (-F.a.dir)) (toE F.c.dir) = π)
    (t u : ℝ) : F.b.pt t ≠ F.c.pt u := by sorry

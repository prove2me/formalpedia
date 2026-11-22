-- Prove2me | Theorems.Thm_ParallelPostulate_ThreeDimensions_angle_at_a1
-- name    : ParallelPostulate.ThreeDimensions.angle_at_a1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:14:32.679176+00:00
-- url     : https://prove2.me/theorems/6dc3dacb-2183-4896-9fe4-bfe21d21f39a
-- title:
--   Three Dimensions: angle at a1
-- statement:
--   The interior angle at `a1`, between `a` run backwards and `c`, is `γ`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L611-L614
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L611-L614

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

theorem ParallelPostulate.ThreeDimensions.angle_at_a1 (β γ : ℝ) (h0 : 0 ≤ γ) (hπ : γ ≤ π) :
    angle (toE (-(angleFigure β γ).a.dir)) (toE (angleFigure β γ).c.dir) = γ := by sorry

-- Prove2me | Theorems.Thm_ParallelPostulate_ThreeDimensions_sin_angle_sum
-- name    : ParallelPostulate.ThreeDimensions.sin_angle_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:12:50.184416+00:00
-- url     : https://prove2.me/theorems/d42c5f03-c236-4670-b2a5-9a0729ef3c30
-- title:
--   Three Dimensions: sin angle sum
-- statement:
--   **The sine of the two interior angles together.** `a` is the direction of the line that
--   falls on the two others, and `b` and `c` are the directions of the two others, both to the left
--   of `a`. With `β` the angle from `a` to `b`, and `γ` the angle from `a` run backwards to `c`:
--
--       sin (β + γ) · |b| · |c| = cross b c .
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L684-L710
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L684-L710

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

theorem ParallelPostulate.ThreeDimensions.sin_angle_sum (a b c : ℝ × ℝ) (hab : 0 < cross a b) (hac : 0 < cross a c) :
    sin (angle (toE a) (toE b) + angle (toE (-a)) (toE c)) * (‖toE b‖ * ‖toE c‖)
      = cross b c := by sorry

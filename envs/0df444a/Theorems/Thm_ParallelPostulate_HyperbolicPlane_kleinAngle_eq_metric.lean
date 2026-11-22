-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_kleinAngle_eq_metric
-- name    : ParallelPostulate.HyperbolicPlane.kleinAngle_eq_metric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:15:43.637346+00:00
-- url     : https://prove2.me/theorems/6fe6397f-600a-4953-9097-f670f7d78a16
-- title:
--   Hyperbolic Plane: klein Angle eq metric
-- statement:
--   **`kleinAngle` is the angle of Klein's metric.** At a point of the plane, the angle
--   between the directions to `A` and to `B` is made from `kleinMetric` as Mathlib makes the angle
--   of Euclid from the inner product.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L2023-L2040
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L2023-L2040

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
open ParallelPostulate.HyperbolicPlane
open Pairs
open Real

theorem ParallelPostulate.HyperbolicPlane.kleinAngle_eq_metric {κ : ℝ} {P : ℝ × ℝ} (hP : P ∈ plane κ) (A B : ℝ × ℝ) :
    kleinAngle κ P A B = arccos (kleinMetric κ P (A - P) (B - P)
      / (√(kleinMetric κ P (A - P) (A - P)) * √(kleinMetric κ P (B - P) (B - P)))) := by sorry

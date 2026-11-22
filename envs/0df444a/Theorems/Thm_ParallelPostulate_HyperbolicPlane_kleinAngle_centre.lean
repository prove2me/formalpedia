-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_kleinAngle_centre
-- name    : ParallelPostulate.HyperbolicPlane.kleinAngle_centre
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:13:22.326822+00:00
-- url     : https://prove2.me/theorems/55dec1b7-a9b6-4b98-a803-240f2c83393e
-- title:
--   Hyperbolic Plane: klein Angle centre
-- statement:
--   **At `(0, 0)` it is the angle of Euclid, under any bound.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1675-L1681
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1675-L1681

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

theorem ParallelPostulate.HyperbolicPlane.kleinAngle_centre (κ : ℝ) (A B : ℝ × ℝ) :
    kleinAngle κ (0, 0) A B
      = InnerProductGeometry.angle (!₂[A.1, A.2] : EuclideanSpace ℝ (Fin 2)) !₂[B.1, B.2] := by sorry

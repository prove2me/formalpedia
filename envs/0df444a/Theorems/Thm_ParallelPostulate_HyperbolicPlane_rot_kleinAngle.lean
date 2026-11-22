-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_rot_kleinAngle
-- name    : ParallelPostulate.HyperbolicPlane.rot_kleinAngle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:13:29.552253+00:00
-- url     : https://prove2.me/theorems/ae0c593d-2d96-47c0-8ed6-f925ea25c9e1
-- title:
--   Hyperbolic Plane: rot klein Angle
-- statement:
--   **Theorem H13. Turning keeps angles.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1736-L1738
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1736-L1738

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

theorem ParallelPostulate.HyperbolicPlane.rot_kleinAngle {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) (κ : ℝ) (P A B : ℝ × ℝ) :
    kleinAngle κ (rot c s P) (rot c s A) (rot c s B) = kleinAngle κ P A B := by sorry

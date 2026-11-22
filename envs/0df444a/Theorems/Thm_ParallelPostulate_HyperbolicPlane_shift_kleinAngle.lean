-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_shift_kleinAngle
-- name    : ParallelPostulate.HyperbolicPlane.shift_kleinAngle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:13:22.679676+00:00
-- url     : https://prove2.me/theorems/95910aa6-8ee7-4397-884b-52235a82f2c0
-- title:
--   Hyperbolic Plane: shift klein Angle
-- statement:
--   **Theorem H13. The motion along the first axis keeps angles.** For three points of the
--   plane, the angle at the first between the two others is the same after the motion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1704-L1733
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1704-L1733

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

theorem ParallelPostulate.HyperbolicPlane.shift_kleinAngle {κ a w : ℝ} (hκ : κ ≤ 0) (hw : w ^ 2 = 1 + κ * a ^ 2) (hw0 : w ≠ 0)
    {P A B : ℝ × ℝ} (hP : P ∈ plane κ) (hA : A ∈ plane κ) (hB : B ∈ plane κ) :
    kleinAngle κ (shift κ a w P) (shift κ a w A) (shift κ a w B) = kleinAngle κ P A B := by sorry

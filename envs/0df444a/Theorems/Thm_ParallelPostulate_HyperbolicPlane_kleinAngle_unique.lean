-- Prove2me | Theorems.Thm_ParallelPostulate_HyperbolicPlane_kleinAngle_unique
-- name    : ParallelPostulate.HyperbolicPlane.kleinAngle_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:15:42.837192+00:00
-- url     : https://prove2.me/theorems/71812530-3930-4241-8aca-6bf8b9c07716
-- title:
--   Hyperbolic Plane: klein Angle unique
-- statement:
--   **`kleinAngle` is the only angle that the motions keep and that is the angle of Euclid at
--   `(0, 0)`.** Let `θ` give a number to three points of the plane. If turning and the motion along
--   the first axis keep `θ`, and at `(0, 0)` it is the angle of Euclid in Mathlib's sense, then it
--   is `kleinAngle`. The proof moves the vertex to `(0, 0)` with Theorem H15.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1776-L1803
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ParallelPostulate.lean#L1776-L1803

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

theorem ParallelPostulate.HyperbolicPlane.kleinAngle_unique {κ : ℝ} (hκ : κ ≤ 0) (θ : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ → ℝ)
    (hshift : ∀ a w : ℝ, w ^ 2 = 1 + κ * a ^ 2 → 0 < w → ∀ P A B : ℝ × ℝ,
      P ∈ plane κ → A ∈ plane κ → B ∈ plane κ →
        θ (shift κ a w P) (shift κ a w A) (shift κ a w B) = θ P A B)
    (hrot : ∀ c s : ℝ, c ^ 2 + s ^ 2 = 1 → ∀ P A B : ℝ × ℝ,
      P ∈ plane κ → A ∈ plane κ → B ∈ plane κ →
        θ (rot c s P) (rot c s A) (rot c s B) = θ P A B)
    (hcentre : ∀ A B : ℝ × ℝ, A ∈ plane κ → B ∈ plane κ →
      θ (0, 0) A B
        = InnerProductGeometry.angle (!₂[A.1, A.2] : EuclideanSpace ℝ (Fin 2)) !₂[B.1, B.2])
    {P A B : ℝ × ℝ} (hP : P ∈ plane κ) (hA : A ∈ plane κ) (hB : B ∈ plane κ) :
    θ P A B = kleinAngle κ P A B := by sorry

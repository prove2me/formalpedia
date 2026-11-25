-- Prove2me | Theorems.Thm_Planks_planks_not_cover_ball
-- name    : Planks.planks_not_cover_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:37:43.515288+00:00
-- url     : https://prove2.me/theorems/ae48e2db-d733-5c01-88a9-6ae9c1d6ce40
-- title:
--   Planks: planks not cover ball
-- statement:
--   **Main theorem.** Let `x₁, …, xₙ` be an orthonormal basis of `ℝⁿ` and `ℓ₁, …, ℓₙ` linear
--   functionals with `ℓᵢ(xᵢ) = 1`. Then the planks `Pᵢ = {z : |ℓᵢ(z)| < 1}` do not cover the
--   closed Euclidean ball of radius `√n` centred at the origin.
--
--   Source: https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/Planks.lean#L307-L320
-- source:
--   https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/Planks.lean#L307-L320

module
public import Mathlib
public import Definitions.Def_BallPlank_Planks
set_option autoImplicit true
@[expose] public section
public section
open scoped RealInnerProductSpace
open Classical
noncomputable section
open Planks
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι]

theorem Planks.planks_not_cover_ball (n : ℕ)
    (x : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (ℓ : Fin n → Module.Dual ℝ (EuclideanSpace ℝ (Fin n)))
    (h : ∀ i, ℓ i (x i) = 1) :
    ¬ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt n) ⊆ ⋃ i, plank (ℓ i)) := by sorry

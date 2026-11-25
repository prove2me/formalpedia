-- Prove2me | Theorems.Thm_PlankProblem_davenport_conjecture
-- name    : PlankProblem.davenport_conjecture
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:48:50.967286+00:00
-- url     : https://prove2.me/theorems/16dae70d-c838-451c-aa39-6a5654cb1938
-- title:
--   Plank Problem: davenport conjecture
-- statement:
--   Davenport's problem for centrally symmetric convex bodies.
--
--   Source: https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/BallPlankFinal.lean#L148-L313
-- source:
--   https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/BallPlankFinal.lean#L148-L313

module
public import Definitions.Def_BallPlank_ShiftedPlanks
public import Definitions.Def_BallPlank_BallPlankFinal
set_option autoImplicit true
@[expose] public section
public section
open Set
open scoped BigOperators InnerProductSpace Pointwise
noncomputable section
open PlankProblem
variable {n : ℕ}
local notation "Rn" => EuclideanSpace ℝ (Fin n)

theorem PlankProblem.davenport_conjecture
    (K : Set Rn)
    (hK : IsConvexBody K)
    (hsymm : IsCentrallySymmetric K)
    (f : Fin n → (Rn →ₗ[ℝ] ℝ))
    (hf : ∀ i, f i ≠ 0)
    (c : Fin n → ℝ) :
    ∃ t : Rn,
      homothet t (1 / (n + 1 : ℝ)) K ⊆ K ∧
      ∀ i x,
        x ∈ interior (homothet t (1 / (n + 1 : ℝ)) K) →
        f i x ≠ c i := by sorry

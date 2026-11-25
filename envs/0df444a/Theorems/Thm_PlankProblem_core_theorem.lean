-- Prove2me | Theorems.Thm_PlankProblem_core_theorem
-- name    : PlankProblem.core_theorem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:47:31.627237+00:00
-- url     : https://prove2.me/theorems/dc1f1ffa-2aed-4b5e-98e4-1b653dd90534
-- title:
--   Plank Problem: core theorem
-- statement:
--   The core theorem: if `X` is an orthonormal basis of `ℝⁿ` and `ℓᵢ(Xᵢ) = 1`, then for any
--   centres `cᵢ` there is a point `z` of the ball `√n · B₂ⁿ` with `|ℓᵢ(z) - cᵢ| ≥ 1` for all `i`,
--   i.e. the planks `{|ℓᵢ - cᵢ| < 1}` do not cover `√n · B₂ⁿ`.
--
--   Source: https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/BallPlankFinal.lean#L75-L85
-- source:
--   https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/BallPlankFinal.lean#L75-L85

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

theorem PlankProblem.core_theorem
    (X : OrthonormalBasis (Fin n) ℝ Rn)
    (ℓ : Fin n → (Rn →ₗ[ℝ] ℝ))
    (hℓ : ∀ i, ℓ i (X i) = 1)
    (c : Fin n → ℝ) :
    ∃ z : Rn,
      ‖z‖ ≤ Real.sqrt (n : ℝ) ∧
      ∀ i, 1 ≤ |ℓ i z - c i| := by sorry

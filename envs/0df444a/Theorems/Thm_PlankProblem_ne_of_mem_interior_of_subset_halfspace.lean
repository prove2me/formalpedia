-- Prove2me | Theorems.Thm_PlankProblem_ne_of_mem_interior_of_subset_halfspace
-- name    : PlankProblem.ne_of_mem_interior_of_subset_halfspace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:47:16.188822+00:00
-- url     : https://prove2.me/theorems/68711bd6-a2c3-4665-8349-f2505ab6c1e0
-- title:
--   Plank Problem: ne of mem interior of subset halfspace
-- statement:
--   If a set lies in the closed half-space `{c ≤ f}` of a nonzero functional, then its interior
--   misses the hyperplane `{f = c}`.
--
--   Source: https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/BallPlankFinal.lean#L126-L145
-- source:
--   https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/BallPlankFinal.lean#L126-L145

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

theorem PlankProblem.ne_of_mem_interior_of_subset_halfspace {A : Set Rn} {f : Rn →ₗ[ℝ] ℝ} (hf : f ≠ 0) {c : ℝ}
    (hA : A ⊆ {x | c ≤ f x}) {x : Rn} (hx : x ∈ interior A) : f x ≠ c := by sorry

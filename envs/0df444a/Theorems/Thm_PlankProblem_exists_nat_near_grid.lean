-- Prove2me | Theorems.Thm_PlankProblem_exists_nat_near_grid
-- name    : PlankProblem.exists_nat_near_grid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:47:15.067713+00:00
-- url     : https://prove2.me/theorems/1c43131b-856e-4215-a5d5-27fd8fa4f56a
-- title:
--   Plank Problem: exists nat near grid
-- statement:
--   Grid covering: the closed interval `[α, α + k s]` is covered by the `k` closed intervals of
--   radius `s/2` centred at `α + (t + 1/2) s`, `t < k`.
--
--   Source: https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/BallPlankFinal.lean#L319-L340
-- source:
--   https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/BallPlankFinal.lean#L319-L340

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

theorem PlankProblem.exists_nat_near_grid {x α s : ℝ} {k : ℕ} (hk : 1 ≤ k) (hs : 0 ≤ s) (hα : α ≤ x)
    (hx : x ≤ α + k * s) : ∃ t : ℕ, t < k ∧ |x - (α + (t + 1 / 2) * s)| ≤ s / 2 := by sorry

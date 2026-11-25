-- Prove2me | Theorems.Thm_PlankProblem_sum_abs_le_card_of_norm_le
-- name    : PlankProblem.sum_abs_le_card_of_norm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:47:09.589719+00:00
-- url     : https://prove2.me/theorems/0b3df392-f52e-4363-90af-6d4b2f40843d
-- title:
--   Plank Problem: sum abs le card of norm le
-- statement:
--   Cauchy–Schwarz: `∑ |zⱼ| ≤ card ι` whenever `‖z‖ ≤ √(card ι)`.
--
--   Source: https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/BallPlankFinal.lean#L343-L355
-- source:
--   https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/BallPlankFinal.lean#L343-L355

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

theorem PlankProblem.sum_abs_le_card_of_norm_le {ι : Type*} [Fintype ι] (z : EuclideanSpace ℝ ι)
    (hz : ‖z‖ ≤ Real.sqrt (Fintype.card ι)) : ∑ j, |z j| ≤ Fintype.card ι := by sorry

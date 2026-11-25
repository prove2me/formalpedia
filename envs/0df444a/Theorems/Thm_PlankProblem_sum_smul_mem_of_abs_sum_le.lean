-- Prove2me | Theorems.Thm_PlankProblem_sum_smul_mem_of_abs_sum_le
-- name    : PlankProblem.sum_smul_mem_of_abs_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:47:13.080268+00:00
-- url     : https://prove2.me/theorems/d8274e11-8d08-4c03-8918-4c262f4cfcea
-- title:
--   Plank Problem: sum smul mem of abs sum le
-- statement:
--   A combination `∑ aᵢ vᵢ` with `∑ |aᵢ| ≤ 1` of points of a symmetric convex set containing `0`
--   stays in the set.
--
--   Source: https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/BallPlankFinal.lean#L94-L122
-- source:
--   https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/BallPlankFinal.lean#L94-L122

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

theorem PlankProblem.sum_smul_mem_of_abs_sum_le {ι : Type*} [Fintype ι] {S : Set Rn} (hS : Convex ℝ S)
    (h0 : (0 : Rn) ∈ S) (hneg : ∀ x ∈ S, -x ∈ S) (v : ι → Rn) (hv : ∀ i, v i ∈ S)
    (a : ι → ℝ) (ha : ∑ i, |a i| ≤ 1) : ∑ i, a i • v i ∈ S := by sorry

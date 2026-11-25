-- Prove2me | Theorems.Thm_Planks_norm_sq_sum
-- name    : Planks.norm_sq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:37:51.213742+00:00
-- url     : https://prove2.me/theorems/40d43f84-8da3-4495-bd76-dc5b0d4752cc
-- title:
--   Planks: norm sq sum
-- statement:
--   The Planks construction uses the norm sq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/Planks.lean#L273-L277
-- source:
--   https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/Planks.lean#L273-L277

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
omit [FiniteDimensional ℝ E]

theorem Planks.norm_sq_sum (y : ι → E) (hy : Orthonormal ℝ y) (c : ι → ℝ) :
    ‖∑ i, c i • y i‖ ^ 2 = ∑ i, c i ^ 2 := by sorry

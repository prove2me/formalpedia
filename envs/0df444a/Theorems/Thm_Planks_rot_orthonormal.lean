-- Prove2me | Theorems.Thm_Planks_rot_orthonormal
-- name    : Planks.rot_orthonormal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:38:09.782561+00:00
-- url     : https://prove2.me/theorems/ab1054ec-afe7-494a-8787-adf719c3c42f
-- title:
--   Planks: rot orthonormal
-- statement:
--   The Planks construction uses the rot orthonormal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/Planks.lean#L89-L133
-- source:
--   https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/Planks.lean#L89-L133

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
omit [FiniteDimensional ℝ E] [Fintype ι]

theorem Planks.rot_orthonormal (y : ι → E) (hy : Orthonormal ℝ y) (i j : ι) (hij : i ≠ j) (t : ℝ) :
    Orthonormal ℝ (rot y i j t) := by sorry

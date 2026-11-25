-- Prove2me | Theorems.Thm_Planks_exists_point_outside_planks
-- name    : Planks.exists_point_outside_planks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:38:23.903247+00:00
-- url     : https://prove2.me/theorems/d5a63e97-0cf6-4967-880a-0419ce1cd130
-- title:
--   Planks: exists point outside planks
-- statement:
--   General version: for an orthonormal basis `x` of a finite-dimensional real inner product
--   space and continuous linear functionals with `ℓᵢ(xᵢ) = 1`, some point of norm `≤ √|ι|`
--   satisfies `|ℓᵢ(z)| ≥ 1` for all `i`.
--
--   Source: https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/Planks.lean#L282-L302
-- source:
--   https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/Planks.lean#L282-L302

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

theorem Planks.exists_point_outside_planks (ℓ : ι → E →L[ℝ] ℝ) (x : ι → E) (hx : Orthonormal ℝ x)
    (h : ∀ i, ℓ i (x i) = 1) :
    ∃ z : E, ‖z‖ ≤ Real.sqrt (Fintype.card ι) ∧ ∀ i, 1 ≤ |ℓ i z| := by sorry

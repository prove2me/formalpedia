-- Prove2me | Theorems.Thm_Planks_exists_point_outside_shifted_planks
-- name    : Planks.exists_point_outside_shifted_planks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:42:13.652572+00:00
-- url     : https://prove2.me/theorems/2a05a02e-3dbf-45af-8d74-93856772cbda
-- title:
--   Planks: exists point outside shifted planks
-- statement:
--   Shifted version: for an orthonormal family `x` with `ℓᵢ(xᵢ) = 1` and arbitrary reals `cᵢ`,
--   some point of norm `≤ √|ι|` satisfies `|ℓᵢ(z) - cᵢ| ≥ 1` for all `i`.
--
--   Source: https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/ShiftedPlanks.lean#L84-L104
-- source:
--   https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/ShiftedPlanks.lean#L84-L104

module
public import Definitions.Def_BallPlank_Planks
public import Definitions.Def_BallPlank_ShiftedPlanks
set_option autoImplicit true
@[expose] public section
public section
open scoped RealInnerProductSpace
open Classical
noncomputable section
open Planks
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι]

theorem Planks.exists_point_outside_shifted_planks (ℓ : ι → E →L[ℝ] ℝ) (c : ι → ℝ) (x : ι → E)
    (hx : Orthonormal ℝ x) (h : ∀ i, ℓ i (x i) = 1) :
    ∃ z : E, ‖z‖ ≤ Real.sqrt (Fintype.card ι) ∧ ∀ i, 1 ≤ |ℓ i z - c i| := by sorry

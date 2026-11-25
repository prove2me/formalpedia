-- Prove2me | Theorems.Thm_Planks_exists_minimizer
-- name    : Planks.exists_minimizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:37:39.107802+00:00
-- url     : https://prove2.me/theorems/68bf0015-ced0-4f48-b000-71f368a8e682
-- title:
--   Planks: exists minimizer
-- statement:
--   The Planks construction uses the exists minimizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/Planks.lean#L45-L77
-- source:
--   https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/Planks.lean#L45-L77

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

theorem Planks.exists_minimizer (ℓ : ι → E →L[ℝ] ℝ) (x : ι → E) (hx : Orthonormal ℝ x)
    (h : ∀ i, ℓ i (x i) = 1) :
    ∃ y ∈ admissible ℓ, IsMinOn (objF ℓ) (admissible ℓ) y ∧
      objF ℓ y ≤ Fintype.card ι := by sorry

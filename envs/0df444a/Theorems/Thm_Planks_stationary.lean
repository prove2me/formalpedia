-- Prove2me | Theorems.Thm_Planks_stationary
-- name    : Planks.stationary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:37:13.252905+00:00
-- url     : https://prove2.me/theorems/ca4d26fe-2551-58a3-b9ac-0cd23545c513
-- title:
--   Planks: stationary
-- statement:
--   The Planks construction uses the stationary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/Planks.lean#L136-L203
-- source:
--   https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/Planks.lean#L136-L203

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

theorem Planks.stationary (ℓ : ι → E →L[ℝ] ℝ) (y : ι → E) (hy : y ∈ admissible ℓ)
    (hmin : IsMinOn (objF ℓ) (admissible ℓ) y) (hF : objF ℓ y ≤ Fintype.card ι)
    (i j : ι) (hij : i ≠ j) :
    ((ℓ i (y i))⁻¹) ^ 3 * ℓ i (y j) = ((ℓ j (y j))⁻¹) ^ 3 * ℓ j (y i) := by sorry

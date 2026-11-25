-- Prove2me | Theorems.Thm_Planks_bang
-- name    : Planks.bang
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:37:58.829881+00:00
-- url     : https://prove2.me/theorems/bdb31c53-82d1-4275-a7dd-288c03774522
-- title:
--   Planks: bang
-- statement:
--   The Planks construction uses the bang property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/Planks.lean#L228-L270
-- source:
--   https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/Planks.lean#L228-L270

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

theorem Planks.bang (ℓ : ι → E →L[ℝ] ℝ) (y : ι → E) (hy0 : ∀ i, ℓ i (y i) ≠ 0)
    (hsym : ∀ i j, ((ℓ i (y i))⁻¹) ^ 3 * ℓ i (y j) = ((ℓ j (y j))⁻¹) ^ 3 * ℓ j (y i)) :
    ∃ ε : ι → Bool, ∀ k,
      1 ≤ |ℓ k (∑ i, (sgn (ε i) * (ℓ i (y i))⁻¹) • y i)| := by sorry

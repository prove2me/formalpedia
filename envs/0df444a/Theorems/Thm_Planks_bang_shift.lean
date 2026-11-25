-- Prove2me | Theorems.Thm_Planks_bang_shift
-- name    : Planks.bang_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:42:53.016047+00:00
-- url     : https://prove2.me/theorems/0bd2d787-c3ee-430f-9418-95410fd16ffa
-- title:
--   Planks: bang shift
-- statement:
--   The Planks construction uses the bang shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/ShiftedPlanks.lean#L27-L80
-- source:
--   https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/ShiftedPlanks.lean#L27-L80

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
omit [FiniteDimensional ℝ E]

theorem Planks.bang_shift (ℓ : ι → E →L[ℝ] ℝ) (c : ι → ℝ) (y : ι → E) (hy0 : ∀ i, ℓ i (y i) ≠ 0)
    (hsym : ∀ i j, ((ℓ i (y i))⁻¹) ^ 3 * ℓ i (y j) = ((ℓ j (y j))⁻¹) ^ 3 * ℓ j (y i)) :
    ∃ ε : ι → Bool, ∀ k,
      1 ≤ |ℓ k (∑ i, (sgn (ε i) * (ℓ i (y i))⁻¹) • y i) - c k| := by sorry

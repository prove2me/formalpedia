-- Prove2me | Theorems.Thm_Planks_flip_quad
-- name    : Planks.flip_quad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:37:55.107104+00:00
-- url     : https://prove2.me/theorems/67cfe1c6-dc49-4fdb-82a0-36ec24e4122d
-- title:
--   Planks: flip quad
-- statement:
--   The Planks construction uses the flip quad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/Planks.lean#L206-L225
-- source:
--   https://github.com/akopjan/Palomar-Bang-Ball/blob/e57a2d8d0129b2d7ce3ee45c2064f5080c8c65eb/BallPlank/Planks.lean#L206-L225

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

theorem Planks.flip_quad (M : ι → ι → ℝ) (hM : ∀ i j, M i j = M j i) (s s' : ι → ℝ) (k : ι)
    (hs' : ∀ i, s' i = if i = k then -s k else s i) :
    ∑ i, ∑ j, s' i * s' j * M i j =
      ∑ i, ∑ j, s i * s j * M i j - 4 * s k * ∑ j, s j * M k j + 4 * s k ^ 2 * M k k := by sorry

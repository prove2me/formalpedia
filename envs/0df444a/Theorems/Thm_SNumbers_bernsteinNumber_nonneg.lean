-- Prove2me | Theorems.Thm_SNumbers_bernsteinNumber_nonneg
-- name    : SNumbers.bernsteinNumber_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:48:47.24306+00:00
-- url     : https://prove2.me/theorems/af289071-378c-4e97-8dd4-8c226c08d485
-- title:
--   SNumbers: bernstein Number nonneg
-- statement:
--   The SNumbers construction uses the bernstein Number nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L142-L144
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L142-L144

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Definitions.Def_SNumbers_Bernstein
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem SNumbers.bernsteinNumber_nonneg (S : X →L[𝕜] Y) (n : ℕ) :
    0 ≤ bernsteinNumber S n := by sorry

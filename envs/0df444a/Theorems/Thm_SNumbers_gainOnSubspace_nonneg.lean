-- Prove2me | Theorems.Thm_SNumbers_gainOnSubspace_nonneg
-- name    : SNumbers.gainOnSubspace_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:32:06.768267+00:00
-- url     : https://prove2.me/theorems/388a8b3b-5cd0-4ac4-8779-ddfaceda5e5f
-- title:
--   SNumbers: gain On Subspace nonneg
-- statement:
--   The SNumbers construction uses the gain On Subspace nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L83-L86
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L83-L86

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

theorem SNumbers.gainOnSubspace_nonneg (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) :
    0 ≤ gainOnSubspace S M := by sorry

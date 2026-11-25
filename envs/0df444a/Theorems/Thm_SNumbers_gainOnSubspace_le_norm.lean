-- Prove2me | Theorems.Thm_SNumbers_gainOnSubspace_le_norm
-- name    : SNumbers.gainOnSubspace_le_norm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:17:04.353573+00:00
-- url     : https://prove2.me/theorems/07506835-7caf-4670-8a33-f705794c67b1
-- title:
--   SNumbers: gain On Subspace le norm
-- statement:
--   The SNumbers construction uses the gain On Subspace le norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L103-L115
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L103-L115

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

theorem SNumbers.gainOnSubspace_le_norm (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) :
    gainOnSubspace S M ≤ ‖S‖ := by sorry

-- Prove2me | Theorems.Thm_SNumbers_isStrictSNumberSequence_gelfandNumber
-- name    : SNumbers.isStrictSNumberSequence_gelfandNumber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:26:49.124837+00:00
-- url     : https://prove2.me/theorems/b71836ea-0986-4e6e-9170-e0bebc07acc6
-- title:
--   SNumbers: is Strict SNumber Sequence gelfand Number
-- statement:
--   The SNumbers construction uses the is Strict SNumber Sequence gelfand Number property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L542-L546
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L542-L546

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand
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

theorem SNumbers.isStrictSNumberSequence_gelfandNumber :
    IsStrictSNumberSequence (𝕜 := 𝕜)
        (fun {_X _Y} _ _ _ _ S n => gelfandNumber S n) := by sorry

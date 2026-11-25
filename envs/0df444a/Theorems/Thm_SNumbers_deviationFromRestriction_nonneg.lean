-- Prove2me | Theorems.Thm_SNumbers_deviationFromRestriction_nonneg
-- name    : SNumbers.deviationFromRestriction_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:47:02.390634+00:00
-- url     : https://prove2.me/theorems/80ec8834-1f60-489f-aefb-4a8b56acc89c
-- title:
--   SNumbers: deviation From Restriction nonneg
-- statement:
--   The SNumbers construction uses the deviation From Restriction nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L93-L95
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L93-L95

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

theorem SNumbers.deviationFromRestriction_nonneg (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) :
    0 ≤ deviationFromRestriction S M := by sorry

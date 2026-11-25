-- Prove2me | Theorems.Thm_SNumbers_deviationFromRestriction_le_norm
-- name    : SNumbers.deviationFromRestriction_le_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:27:56.724516+00:00
-- url     : https://prove2.me/theorems/78a25040-9a7b-4f16-bbd5-771b6020e9a8
-- title:
--   SNumbers: deviation From Restriction le norm
-- statement:
--   The SNumbers construction uses the deviation From Restriction le norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L97-L104
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L97-L104

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

theorem SNumbers.deviationFromRestriction_le_norm (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) :
    deviationFromRestriction S M ≤ ‖S‖ := by sorry

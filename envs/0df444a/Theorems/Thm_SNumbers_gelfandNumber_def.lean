-- Prove2me | Theorems.Thm_SNumbers_gelfandNumber_def
-- name    : SNumbers.gelfandNumber_def
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:56:13.212709+00:00
-- url     : https://prove2.me/theorems/a3a97cab-4c83-49cd-b37b-dc3d61486431
-- title:
--   SNumbers: gelfand Number def
-- statement:
--   The SNumbers construction uses the gelfand Number def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L88-L89
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L88-L89

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

theorem SNumbers.gelfandNumber_def (S : X →L[𝕜] Y) (n : ℕ) :
    gelfandNumber S n = sInf (gelfandSet S n) := by sorry

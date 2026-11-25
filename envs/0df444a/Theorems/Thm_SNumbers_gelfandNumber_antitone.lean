-- Prove2me | Theorems.Thm_SNumbers_gelfandNumber_antitone
-- name    : SNumbers.gelfandNumber_antitone
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:23:38.066359+00:00
-- url     : https://prove2.me/theorems/09da6062-2c08-4a5d-bbfa-0857a028138a
-- title:
--   SNumbers: gelfand Number antitone
-- statement:
--   The SNumbers construction uses the gelfand Number antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L162-L164
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L162-L164

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

theorem SNumbers.gelfandNumber_antitone (S : X →L[𝕜] Y) (n : ℕ) :
    gelfandNumber S (n + 1) ≤ gelfandNumber S n := by sorry

-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_antitone
-- name    : SNumbers.approximationNumber_antitone
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:07:53.286113+00:00
-- url     : https://prove2.me/theorems/697ad98c-10ad-45e4-bb72-5a6df208e76c
-- title:
--   SNumbers: approximation Number antitone
-- statement:
--   The SNumbers construction uses the approximation Number antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L120-L122
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L120-L122

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Approximation
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

theorem SNumbers.approximationNumber_antitone (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S (n + 1) ≤ approximationNumber S n := by sorry

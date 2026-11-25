-- Prove2me | Theorems.Thm_SNumbers_bernsteinNumber_def
-- name    : SNumbers.bernsteinNumber_def
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:02:26.123374+00:00
-- url     : https://prove2.me/theorems/373bb358-6e0b-4ab9-94b7-e51b349a74bc
-- title:
--   SNumbers: bernstein Number def
-- statement:
--   The SNumbers construction uses the bernstein Number def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L68-L69
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L68-L69

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

theorem SNumbers.bernsteinNumber_def (S : X →L[𝕜] Y) (n : ℕ) :
    bernsteinNumber S n = sSup (bernsteinSet S n) := by sorry

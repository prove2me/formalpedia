-- Prove2me | Theorems.Thm_SNumbers_bernsteinNumber_add_le
-- name    : SNumbers.bernsteinNumber_add_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:48:41.959229+00:00
-- url     : https://prove2.me/theorems/20ac71d5-8a86-4d93-ab46-b2a3ccf6c39b
-- title:
--   SNumbers: bernstein Number add le
-- statement:
--   The SNumbers construction uses the bernstein Number add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L247-L256
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L247-L256

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

theorem SNumbers.bernsteinNumber_add_le (S T : X →L[𝕜] Y) (n : ℕ) :
    bernsteinNumber (S + T) n ≤ bernsteinNumber S n + ‖T‖ := by sorry

-- Prove2me | Theorems.Thm_SNumbers_bernsteinNumber_comp_comp_le
-- name    : SNumbers.bernsteinNumber_comp_comp_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:16:58.85741+00:00
-- url     : https://prove2.me/theorems/1fc9057e-2a5d-4609-8568-1cb9519bd147
-- title:
--   SNumbers: bernstein Number comp comp le
-- statement:
--   The SNumbers construction uses the bernstein Number comp comp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L439-L469
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L439-L469

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

theorem SNumbers.bernsteinNumber_comp_comp_le
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (n : ℕ) :
    bernsteinNumber (B.comp (S.comp A)) n ≤
      ‖B‖ * bernsteinNumber S n * ‖A‖ := by sorry

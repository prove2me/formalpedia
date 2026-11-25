-- Prove2me | Theorems.Thm_SNumbers_isSNumberSequence_bernsteinNumber
-- name    : SNumbers.isSNumberSequence_bernsteinNumber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:17:28.064722+00:00
-- url     : https://prove2.me/theorems/6df650c5-8d30-4afc-859c-b0f37895250b
-- title:
--   SNumbers: is SNumber Sequence bernstein Number
-- statement:
--   The SNumbers construction uses the is SNumber Sequence bernstein Number property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L473-L482
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L473-L482

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

theorem SNumbers.isSNumberSequence_bernsteinNumber :
    IsSNumberSequence (𝕜 := 𝕜)
        (fun {_X _Y} _ _ _ _ S n => bernsteinNumber S n) := by sorry

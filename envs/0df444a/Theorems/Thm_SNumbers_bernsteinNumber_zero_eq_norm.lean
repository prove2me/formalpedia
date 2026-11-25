-- Prove2me | Theorems.Thm_SNumbers_bernsteinNumber_zero_eq_norm
-- name    : SNumbers.bernsteinNumber_zero_eq_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:48:18.016008+00:00
-- url     : https://prove2.me/theorems/ea47e8a4-9593-4533-84bc-f95662e24603
-- title:
--   SNumbers: bernstein Number zero eq norm
-- statement:
--   The SNumbers construction uses the bernstein Number zero eq norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L170-L185
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L170-L185

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

theorem SNumbers.bernsteinNumber_zero_eq_norm (S : X →L[𝕜] Y) :
    bernsteinNumber S 0 = ‖S‖ := by sorry

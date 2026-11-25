-- Prove2me | Theorems.Thm_SNumbers_isStrictSNumberSequence_kolmogorovNumber
-- name    : SNumbers.isStrictSNumberSequence_kolmogorovNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:09:01.376476+00:00
-- url     : https://prove2.me/theorems/27149560-3e66-47c3-9e67-4041781df5da
-- title:
--   SNumbers: is Strict SNumber Sequence kolmogorov Number
-- statement:
--   The SNumbers construction uses the is Strict SNumber Sequence kolmogorov Number property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L569-L573
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L569-L573

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov
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
variable [CompleteSpace 𝕜]

theorem SNumbers.isStrictSNumberSequence_kolmogorovNumber :
    IsStrictSNumberSequence (𝕜 := 𝕜)
        (fun {_X _Y} _ _ _ _ S n => kolmogorovNumber S n) := by sorry

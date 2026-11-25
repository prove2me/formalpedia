-- Prove2me | Theorems.Thm_SNumbers_kolmogorovNumber_le_deviation
-- name    : SNumbers.kolmogorovNumber_le_deviation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:51:46.47612+00:00
-- url     : https://prove2.me/theorems/b24cc64e-08a1-439b-b138-ec4852f139f9
-- title:
--   SNumbers: kolmogorov Number le deviation
-- statement:
--   The SNumbers construction uses the kolmogorov Number le deviation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L131-L134
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L131-L134

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

theorem SNumbers.kolmogorovNumber_le_deviation {S : X →L[𝕜] Y} {n : ℕ} {V : Submodule 𝕜 Y}
    (hV : Module.rank 𝕜 V ≤ (n : Cardinal)) :
    kolmogorovNumber S n ≤ deviationFromSubspace S V := by sorry

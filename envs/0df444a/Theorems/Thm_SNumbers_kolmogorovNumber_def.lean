-- Prove2me | Theorems.Thm_SNumbers_kolmogorovNumber_def
-- name    : SNumbers.kolmogorovNumber_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:30:21.135544+00:00
-- url     : https://prove2.me/theorems/a9e036d0-f7dd-56c1-89d8-ab1a24c0e65a
-- title:
--   SNumbers: kolmogorov Number def
-- statement:
--   The SNumbers construction uses the kolmogorov Number def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L101-L102
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L101-L102

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

theorem SNumbers.kolmogorovNumber_def (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S n = sInf (kolmogorovSet S n) := by sorry

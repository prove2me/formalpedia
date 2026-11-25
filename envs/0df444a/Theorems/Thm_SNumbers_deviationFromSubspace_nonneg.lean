-- Prove2me | Theorems.Thm_SNumbers_deviationFromSubspace_nonneg
-- name    : SNumbers.deviationFromSubspace_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:03:30.960503+00:00
-- url     : https://prove2.me/theorems/cd76b090-deb0-4333-a55c-d6bf4adfbfa9
-- title:
--   SNumbers: deviation From Subspace nonneg
-- statement:
--   The SNumbers construction uses the deviation From Subspace nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L106-L108
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L106-L108

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

theorem SNumbers.deviationFromSubspace_nonneg (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) :
    0 ≤ deviationFromSubspace S V := by sorry

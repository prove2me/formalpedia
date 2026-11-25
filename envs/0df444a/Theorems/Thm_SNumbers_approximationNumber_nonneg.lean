-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_nonneg
-- name    : SNumbers.approximationNumber_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:42:42.950252+00:00
-- url     : https://prove2.me/theorems/5a2d025d-e926-4fa2-8a01-4a8d0bba9ed2
-- title:
--   SNumbers: approximation Number nonneg
-- statement:
--   The SNumbers construction uses the approximation Number nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L106-L109
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L106-L109

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

theorem SNumbers.approximationNumber_nonneg (S : X →L[𝕜] Y) (n : ℕ) :
    0 ≤ approximationNumber S n := by sorry

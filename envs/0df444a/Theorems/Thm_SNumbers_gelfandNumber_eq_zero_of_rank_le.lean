-- Prove2me | Theorems.Thm_SNumbers_gelfandNumber_eq_zero_of_rank_le
-- name    : SNumbers.gelfandNumber_eq_zero_of_rank_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:06:16.898635+00:00
-- url     : https://prove2.me/theorems/f0e6c368-b0e8-540d-a68c-08838b2a48f9
-- title:
--   SNumbers: gelfand Number eq zero of rank le
-- statement:
--   The SNumbers construction uses the gelfand Number eq zero of rank le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L450-L477
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L450-L477

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand
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

theorem SNumbers.gelfandNumber_eq_zero_of_rank_le {S : X →L[𝕜] Y} {n : ℕ}
    (hS : S.rank ≤ (n : Cardinal)) :
    gelfandNumber S n = 0 := by sorry

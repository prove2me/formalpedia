-- Prove2me | Theorems.Thm_SNumbers_gelfandNumber_le_deviation
-- name    : SNumbers.gelfandNumber_le_deviation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:48:28.262601+00:00
-- url     : https://prove2.me/theorems/bfe02c78-0451-42d5-852c-c403605fb950
-- title:
--   SNumbers: gelfand Number le deviation
-- statement:
--   The SNumbers construction uses the gelfand Number le deviation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L125-L129
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L125-L129

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

theorem SNumbers.gelfandNumber_le_deviation {S : X →L[𝕜] Y} {n : ℕ} {M : Submodule 𝕜 X}
    (hM_closed : IsClosed (M : Set X))
    (hM_rank : Module.rank 𝕜 (X ⧸ M) ≤ (n : Cardinal)) :
    gelfandNumber S n ≤ deviationFromRestriction S M := by sorry

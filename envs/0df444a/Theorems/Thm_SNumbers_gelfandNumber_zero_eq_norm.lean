-- Prove2me | Theorems.Thm_SNumbers_gelfandNumber_zero_eq_norm
-- name    : SNumbers.gelfandNumber_zero_eq_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:08:48.904712+00:00
-- url     : https://prove2.me/theorems/d8c083c0-ca4a-4650-a79b-89b02df1e1d3
-- title:
--   SNumbers: gelfand Number zero eq norm
-- statement:
--   The SNumbers construction uses the gelfand Number zero eq norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L193-L213
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L193-L213

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

theorem SNumbers.gelfandNumber_zero_eq_norm (S : X →L[𝕜] Y) :
    gelfandNumber S 0 = ‖S‖ := by sorry

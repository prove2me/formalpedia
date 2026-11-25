-- Prove2me | Theorems.Thm_P2M_SNumbers_gelfandNumber_antitone__140691ee51a6
-- name    : P2M_SNumbers_gelfandNumber_antitone__140691ee51a6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:15:11.847921+00:00
-- url     : https://prove2.me/theorems/1bdde258-4d6b-4a7a-9430-7cac06ac53db
-- title:
--   P2 M SNumbers gelfand Number antitone  140691ee51a6: P2 M SNumbers gelfand Number antitone  140691ee51a6
-- statement:
--   If `n ≤ m`, then `c_m S ≤ c_n S`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L157-L160
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L157-L160

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

theorem P2M_SNumbers_gelfandNumber_antitone__140691ee51a6 (S : X →L[𝕜] Y) {n m : ℕ} (h : n ≤ m) :
    gelfandNumber S m ≤ gelfandNumber S n := by sorry

alias «SNumbers».«gelfandNumber_antitone'» := P2M_SNumbers_gelfandNumber_antitone__140691ee51a6

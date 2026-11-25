-- Prove2me | Theorems.Thm_SNumbers_additive_gelfandNumber
-- name    : SNumbers.additive_gelfandNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:29:01.197521+00:00
-- url     : https://prove2.me/theorems/286e8467-11c2-485b-a23c-e46f1176e4ad
-- title:
--   SNumbers: additive gelfand Number
-- statement:
--   The Gelfand numbers are additive: `c_{n+m}(S + T) ≤ cₙ(S) + c_m(T)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L549-L551
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L549-L551

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

theorem SNumbers.additive_gelfandNumber :
    Additive (𝕜 := 𝕜) (fun {_X _Y} _ _ _ _ S n => gelfandNumber S n) := by sorry

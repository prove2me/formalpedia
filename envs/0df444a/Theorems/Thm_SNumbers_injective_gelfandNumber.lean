-- Prove2me | Theorems.Thm_SNumbers_injective_gelfandNumber
-- name    : SNumbers.injective_gelfandNumber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:09:27.936479+00:00
-- url     : https://prove2.me/theorems/c0c06de7-be0f-49d9-8a93-bfe37c72e07c
-- title:
--   SNumbers: injective gelfand Number
-- statement:
--   **The Gelfand numbers are an injective `s`-number sequence.**
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Injectivity.lean#L222-L226
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Injectivity.lean#L222-L226

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_Injectivity
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

theorem SNumbers.injective_gelfandNumber :
    Injective (𝕜 := 𝕜) (fun {_X _Y} _ _ _ _ S n => gelfandNumber S n) := by sorry

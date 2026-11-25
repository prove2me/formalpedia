-- Prove2me | Theorems.Thm_SNumbers_surjective_kolmogorovNumber
-- name    : SNumbers.surjective_kolmogorovNumber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:01:56.636703+00:00
-- url     : https://prove2.me/theorems/d6c2f726-f306-5d55-9f70-cf34be105406
-- title:
--   SNumbers: surjective kolmogorov Number
-- statement:
--   **The Kolmogorov numbers are a surjective `s`-number sequence.**
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Injectivity.lean#L282-L286
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Injectivity.lean#L282-L286

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

theorem SNumbers.surjective_kolmogorovNumber :
    Surjective (𝕜 := 𝕜) (fun {_X _Y} _ _ _ _ S n => kolmogorovNumber S n) := by sorry

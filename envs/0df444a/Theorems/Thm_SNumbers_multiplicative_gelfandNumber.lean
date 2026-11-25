-- Prove2me | Theorems.Thm_SNumbers_multiplicative_gelfandNumber
-- name    : SNumbers.multiplicative_gelfandNumber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:29:37.753596+00:00
-- url     : https://prove2.me/theorems/f2136a7e-8542-5d25-bad1-fcff526be32c
-- title:
--   SNumbers: multiplicative gelfand Number
-- statement:
--   The Gelfand numbers are multiplicative: `c_{n+m}(S ∘ T) ≤ cₙ(S) · c_m(T)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L554-L556
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L554-L556

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

theorem SNumbers.multiplicative_gelfandNumber :
    Multiplicative (𝕜 := 𝕜) (fun {_X _Y} _ _ _ _ S n => gelfandNumber S n) := by sorry

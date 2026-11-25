-- Prove2me | Theorems.Thm_SNumbers_additive_kolmogorovNumber
-- name    : SNumbers.additive_kolmogorovNumber
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T03:01:16.162984+00:00
-- url     : https://prove2.me/theorems/99351bf0-4452-4d2d-a7e7-f185a3c2d40d
-- title:
--   SNumbers: additive kolmogorov Number
-- statement:
--   The Kolmogorov numbers are additive: `d_{n+m}(S + T) ≤ dₙ(S) + d_m(T)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L577-L579
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L577-L579

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
variable [CompleteSpace 𝕜]
omit [CompleteSpace 𝕜]

theorem SNumbers.additive_kolmogorovNumber :
    Additive (𝕜 := 𝕜) (fun {_X _Y} _ _ _ _ S n => kolmogorovNumber S n) := by sorry

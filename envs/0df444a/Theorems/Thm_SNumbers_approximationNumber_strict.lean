-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_strict
-- name    : SNumbers.approximationNumber_strict
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:21:12.618818+00:00
-- url     : https://prove2.me/theorems/5d537fe3-9074-48cd-b482-1c661770a258
-- title:
--   SNumbers: approximation Number strict
-- statement:
--   (S5') Strict normalisation: `approximationNumber (id_X) n = 1` whenever
--   `dim X > n`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L320-L374
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L320-L374

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
variable [CompleteSpace 𝕜]

theorem SNumbers.approximationNumber_strict {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (n : ℕ) (h : (n : Cardinal) < Module.rank 𝕜 X) :
    approximationNumber (ContinuousLinearMap.id 𝕜 X) n = 1 := by sorry

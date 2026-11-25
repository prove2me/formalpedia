-- Prove2me | Theorems.Thm_SNumbers_gelfandNumber_strict
-- name    : SNumbers.gelfandNumber_strict
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:26:39.902014+00:00
-- url     : https://prove2.me/theorems/128a8f3e-a01a-4a00-8e71-9d2b9682fd6e
-- title:
--   SNumbers: gelfand Number strict
-- statement:
--   (S5') Strict normalisation: `gelfandNumber (id_X) n = 1` whenever
--   `n < Module.finrank 𝕜 X`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L491-L519
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L491-L519

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

theorem SNumbers.gelfandNumber_strict {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (n : ℕ) (h : (n : Cardinal) < Module.rank 𝕜 X) :
    gelfandNumber (ContinuousLinearMap.id 𝕜 X) n = 1 := by sorry

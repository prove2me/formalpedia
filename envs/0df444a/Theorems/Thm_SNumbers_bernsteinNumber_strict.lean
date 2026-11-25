-- Prove2me | Theorems.Thm_SNumbers_bernsteinNumber_strict
-- name    : SNumbers.bernsteinNumber_strict
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:17:10.188209+00:00
-- url     : https://prove2.me/theorems/e744d49a-08e8-4d10-8f0c-27599e997d6a
-- title:
--   SNumbers: bernstein Number strict
-- statement:
--   (S5') Strict normalisation: `bernsteinNumber (id_X) n = 1` whenever
--   `dim X > n`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L322-L340
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L322-L340

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Definitions.Def_SNumbers_Bernstein
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

theorem SNumbers.bernsteinNumber_strict {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (n : ℕ) (h : (n : Cardinal) < Module.rank 𝕜 X) :
    bernsteinNumber (ContinuousLinearMap.id 𝕜 X) n = 1 := by sorry

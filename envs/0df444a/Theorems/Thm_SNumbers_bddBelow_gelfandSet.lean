-- Prove2me | Theorems.Thm_SNumbers_bddBelow_gelfandSet
-- name    : SNumbers.bddBelow_gelfandSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:22:51.5381+00:00
-- url     : https://prove2.me/theorems/5fbb0b5e-e1f4-4c29-b271-baf4b8986e6a
-- title:
--   SNumbers: bdd Below gelfand Set
-- statement:
--   The set of admissible deviations is bounded below by `0`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L121-L123
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L121-L123

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

theorem SNumbers.bddBelow_gelfandSet (S : X →L[𝕜] Y) (n : ℕ) :
    BddBelow (gelfandSet S n) := by sorry

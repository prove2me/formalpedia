-- Prove2me | Theorems.Thm_SNumbers_gelfandSet_subset
-- name    : SNumbers.gelfandSet_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:01:22.388322+00:00
-- url     : https://prove2.me/theorems/d72f6bcd-2cd3-5747-9dd1-1fcbf39b65ca
-- title:
--   SNumbers: gelfand Set subset
-- statement:
--   Raising `n` allows subspaces of larger codimension, hence more deviations
--   become admissible.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L151-L154
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L151-L154

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

theorem SNumbers.gelfandSet_subset (S : X →L[𝕜] Y) {n m : ℕ} (h : n ≤ m) :
    gelfandSet S n ⊆ gelfandSet S m := by sorry

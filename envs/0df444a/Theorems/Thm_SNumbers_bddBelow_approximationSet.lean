-- Prove2me | Theorems.Thm_SNumbers_bddBelow_approximationSet
-- name    : SNumbers.bddBelow_approximationSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:07:38.419852+00:00
-- url     : https://prove2.me/theorems/46b2294c-647d-4b38-b0d6-a9d8068e4536
-- title:
--   SNumbers: bdd Below approximation Set
-- statement:
--   The approximation set is bounded below by `0`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L93-L95
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Approximation.lean#L93-L95

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

theorem SNumbers.bddBelow_approximationSet (S : X →L[𝕜] Y) (n : ℕ) :
    BddBelow (approximationSet S n) := by sorry

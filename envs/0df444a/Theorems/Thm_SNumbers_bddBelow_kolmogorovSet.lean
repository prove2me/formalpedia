-- Prove2me | Theorems.Thm_SNumbers_bddBelow_kolmogorovSet
-- name    : SNumbers.bddBelow_kolmogorovSet
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:26:58.335228+00:00
-- url     : https://prove2.me/theorems/6132972c-38a1-4f9e-9100-4ca16bd0d101
-- title:
--   SNumbers: bdd Below kolmogorov Set
-- statement:
--   The set of admissible deviations is bounded below by `0`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L127-L129
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L127-L129

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

theorem SNumbers.bddBelow_kolmogorovSet (S : X →L[𝕜] Y) (n : ℕ) :
    BddBelow (kolmogorovSet S n) := by sorry

-- Prove2me | Theorems.Thm_SNumbers_kolmogorovSet_subset
-- name    : SNumbers.kolmogorovSet_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:06:57.009117+00:00
-- url     : https://prove2.me/theorems/20fee3dd-de5e-4156-8207-f384e8c857c5
-- title:
--   SNumbers: kolmogorov Set subset
-- statement:
--   Raising `n` allows subspaces of larger dimension, hence more deviations
--   become admissible.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L157-L160
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L157-L160

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

theorem SNumbers.kolmogorovSet_subset (S : X →L[𝕜] Y) {n m : ℕ} (h : n ≤ m) :
    kolmogorovSet S n ⊆ kolmogorovSet S m := by sorry

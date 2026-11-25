-- Prove2me | Theorems.Thm_SNumbers_entropySet_subset
-- name    : SNumbers.entropySet_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:17:35.206152+00:00
-- url     : https://prove2.me/theorems/a1541bb6-dad8-5a12-b388-b0b15bc66bf6
-- title:
--   SNumbers: entropy Set subset
-- statement:
--   Raising `n` allows more balls, hence more radii become admissible.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L191-L194
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L191-L194

module
public import Definitions.Def_SNumbers_Basic
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Definitions.Def_SNumbers_Entropy
set_option autoImplicit true
@[expose] public section
public section
universe u
open Filter Topology
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem SNumbers.entropySet_subset (S : X →L[𝕜] Y) {n m : ℕ} (h : n ≤ m) :
    entropySet S n ⊆ entropySet S m := by sorry

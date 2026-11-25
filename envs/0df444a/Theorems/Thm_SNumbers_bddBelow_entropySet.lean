-- Prove2me | Theorems.Thm_SNumbers_bddBelow_entropySet
-- name    : SNumbers.bddBelow_entropySet
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:37:14.452362+00:00
-- url     : https://prove2.me/theorems/faa6e37f-72f0-4644-8406-6ddc08f1db91
-- title:
--   SNumbers: bdd Below entropy Set
-- statement:
--   The entropy set is bounded below by `0`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L164-L166
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L164-L166

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

theorem SNumbers.bddBelow_entropySet (S : X →L[𝕜] Y) (n : ℕ) :
    BddBelow (entropySet S n) := by sorry

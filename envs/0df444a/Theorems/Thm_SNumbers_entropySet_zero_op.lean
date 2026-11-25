-- Prove2me | Theorems.Thm_SNumbers_entropySet_zero_op
-- name    : SNumbers.entropySet_zero_op
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:18:21.93219+00:00
-- url     : https://prove2.me/theorems/f171db70-ec68-4be3-b6df-e4fa518ac249
-- title:
--   SNumbers: entropy Set zero op
-- statement:
--   For the zero operator every positive radius is admissible.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L215-L220
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L215-L220

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

theorem SNumbers.entropySet_zero_op (n : ℕ) :
    entropySet (0 : X →L[𝕜] Y) n = Set.Ioi 0 := by sorry

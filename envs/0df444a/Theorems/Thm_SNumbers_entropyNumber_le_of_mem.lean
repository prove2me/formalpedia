-- Prove2me | Theorems.Thm_SNumbers_entropyNumber_le_of_mem
-- name    : SNumbers.entropyNumber_le_of_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:05:06.561962+00:00
-- url     : https://prove2.me/theorems/ac52fa63-9ea3-463a-b4c9-1a40cae0e31e
-- title:
--   SNumbers: entropy Number le of mem
-- statement:
--   Every admissible radius bounds the entropy number from above.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L169-L172
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L169-L172

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

theorem SNumbers.entropyNumber_le_of_mem {S : X →L[𝕜] Y} {n : ℕ} {ε : ℝ}
    (hε : ε ∈ entropySet S n) :
    entropyNumber S n ≤ ε := by sorry

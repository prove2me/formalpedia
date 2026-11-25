-- Prove2me | Theorems.Thm_SNumbers_entropyNumber_add_le
-- name    : SNumbers.entropyNumber_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:18:06.707866+00:00
-- url     : https://prove2.me/theorems/9f37cb98-f354-5a2c-aeff-bc2b58d0fefa
-- title:
--   SNumbers: entropy Number add le
-- statement:
--   **(S2) Subadditivity**, the case `m = 0` of additivity together with
--   `e_0 T ≤ ‖T‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L269-L273
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L269-L273

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

theorem SNumbers.entropyNumber_add_le (S T : X →L[𝕜] Y) (n : ℕ) :
    entropyNumber (S + T) n ≤ entropyNumber S n + ‖T‖ := by sorry

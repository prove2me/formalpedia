-- Prove2me | Theorems.Thm_P2M_SNumbers_entropyNumber_antitone__7948be0d85af
-- name    : P2M_SNumbers_entropyNumber_antitone__7948be0d85af
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:37:14.980182+00:00
-- url     : https://prove2.me/theorems/d740182f-9c89-4113-8b1c-4ad720e88658
-- title:
--   P2 M SNumbers entropy Number antitone  7948be0d85af: P2 M SNumbers entropy Number antitone  7948be0d85af
-- statement:
--   If `n ≤ m`, then `e_m S ≤ e_n S`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L197-L200
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L197-L200

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

theorem P2M_SNumbers_entropyNumber_antitone__7948be0d85af (S : X →L[𝕜] Y) {n m : ℕ} (h : n ≤ m) :
    entropyNumber S m ≤ entropyNumber S n := by sorry

alias «SNumbers».«entropyNumber_antitone'» := P2M_SNumbers_entropyNumber_antitone__7948be0d85af

-- Prove2me | Theorems.Thm_SNumbers_entropyNumber_additive
-- name    : SNumbers.entropyNumber_additive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:18:17.073318+00:00
-- url     : https://prove2.me/theorems/e36c32c1-ccb6-4207-9ad6-ec41d89221ff
-- title:
--   SNumbers: entropy Number additive
-- statement:
--   **Additivity of the entropy numbers**: `e_{n+m}(S + T) ≤ e_n S + e_m T`.
--   The budget of balls multiplies, so the indices add.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L256-L265
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L256-L265

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

theorem SNumbers.entropyNumber_additive (S T : X →L[𝕜] Y) (n m : ℕ) :
    entropyNumber (S + T) (n + m) ≤ entropyNumber S n + entropyNumber T m := by sorry

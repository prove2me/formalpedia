-- Prove2me | Theorems.Thm_SNumbers_entropyNumber_comp_le
-- name    : SNumbers.entropyNumber_comp_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:04:50.681811+00:00
-- url     : https://prove2.me/theorems/d15cf198-817a-5935-b022-3744ab4a09c2
-- title:
--   SNumbers: entropy Number comp le
-- statement:
--   `e_n (B ∘ S) ≤ ‖B‖ · e_n S`. This is the half of the ideal property (S3)
--   that costs nothing; see `entropyNumber_comp_comp_le` for the full statement.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L299-L307
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L299-L307

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

theorem SNumbers.entropyNumber_comp_le (B : Y →L[𝕜] Z) (S : X →L[𝕜] Y) (n : ℕ) :
    entropyNumber (B.comp S) n ≤ ‖B‖ * entropyNumber S n := by sorry

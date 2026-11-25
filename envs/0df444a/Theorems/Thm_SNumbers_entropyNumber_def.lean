-- Prove2me | Theorems.Thm_SNumbers_entropyNumber_def
-- name    : SNumbers.entropyNumber_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:01:16.625276+00:00
-- url     : https://prove2.me/theorems/b31ffabd-ef17-41a0-bca0-5397712bfb41
-- title:
--   SNumbers: entropy Number def
-- statement:
--   The SNumbers construction uses the entropy Number def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L138-L139
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L138-L139

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

theorem SNumbers.entropyNumber_def (S : X →L[𝕜] Y) (n : ℕ) :
    entropyNumber S n = sInf (entropySet S n) := by sorry

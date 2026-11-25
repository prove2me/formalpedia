-- Prove2me | Theorems.Thm_SNumbers_entropyNumber_antitone
-- name    : SNumbers.entropyNumber_antitone
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:17:56.593573+00:00
-- url     : https://prove2.me/theorems/854a1933-f943-4756-a351-5cc4fb17b7d9
-- title:
--   SNumbers: entropy Number antitone
-- statement:
--   The SNumbers construction uses the entropy Number antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L202-L204
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Entropy.lean#L202-L204

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

theorem SNumbers.entropyNumber_antitone (S : X →L[𝕜] Y) (n : ℕ) :
    entropyNumber S (n + 1) ≤ entropyNumber S n := by sorry

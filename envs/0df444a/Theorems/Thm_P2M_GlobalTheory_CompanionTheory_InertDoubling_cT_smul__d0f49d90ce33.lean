-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_InertDoubling_cT_smul__d0f49d90ce33
-- name    : P2M_GlobalTheory_CompanionTheory_InertDoubling_cT_smul__d0f49d90ce33
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:04:00.830341+00:00
-- url     : https://prove2.me/theorems/3d077dbb-c916-4d82-a464-9ec72f756a07
-- title:
--   P2 M Global Theory Companion Theory Inert Doubling c T smul  d0f49d90ce33: P2 M Global Theory Companion Theory Inert Doubling c T smul  d0f49d90ce33
-- statement:
--   The P2 M Global Theory Companion Theory Inert Doubling c T smul  d0f49d90ce33 construction uses the P2 M Global Theory Companion Theory Inert Doubling c T smul  d0f49d90ce33 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CompletionExists.lean#L50-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CompletionExists.lean#L50-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CompletionExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.Doubling GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertDoubling
variable {L : Type} [Field L] {σ : L →+* L} {m p : Type}

theorem P2M_GlobalTheory_CompanionTheory_InertDoubling_cT_smul__d0f49d90ce33 (c : L) (M : Matrix m p L) : cT σ (c • M) = σ c • cT σ M := by sorry

alias «GlobalTheory».«CompanionTheory».«InertDoubling».«cT_smul'» := P2M_GlobalTheory_CompanionTheory_InertDoubling_cT_smul__d0f49d90ce33

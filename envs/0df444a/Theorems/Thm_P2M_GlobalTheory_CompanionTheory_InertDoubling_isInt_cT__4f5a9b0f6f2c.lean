-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_InertDoubling_isInt_cT__4f5a9b0f6f2c
-- name    : P2M_GlobalTheory_CompanionTheory_InertDoubling_isInt_cT__4f5a9b0f6f2c
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:04:49.413365+00:00
-- url     : https://prove2.me/theorems/146413e6-2f95-47f9-b2c7-e4b91b921126
-- title:
--   P2 M Global Theory Companion Theory Inert Doubling is Int c T  4f5a9b0f6f2c: P2 M Global Theory Companion Theory Inert Doubling is Int c T  4f5a9b0f6f2c
-- statement:
--   The P2 M Global Theory Companion Theory Inert Doubling is Int c T  4f5a9b0f6f2c construction uses the P2 M Global Theory Companion Theory Inert Doubling is Int c T  4f5a9b0f6f2c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CompletionExists.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CompletionExists.lean#L86-L90

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
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem P2M_GlobalTheory_CompanionTheory_InertDoubling_isInt_cT__4f5a9b0f6f2c {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {m p : Type} {A : Matrix m p L} (h : IsInt A) :
    IsInt (cT σ A) := by sorry

alias «GlobalTheory».«CompanionTheory».«InertDoubling».«isInt_cT'» := P2M_GlobalTheory_CompanionTheory_InertDoubling_isInt_cT__4f5a9b0f6f2c

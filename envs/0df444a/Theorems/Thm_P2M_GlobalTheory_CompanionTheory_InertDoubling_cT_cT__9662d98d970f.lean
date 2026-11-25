-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_InertDoubling_cT_cT__9662d98d970f
-- name    : P2M_GlobalTheory_CompanionTheory_InertDoubling_cT_cT__9662d98d970f
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:03:40.170189+00:00
-- url     : https://prove2.me/theorems/db32cfca-6bd0-4c0c-939e-536a78e47475
-- title:
--   P2 M Global Theory Companion Theory Inert Doubling c T c T  9662d98d970f: P2 M Global Theory Companion Theory Inert Doubling c T c T  9662d98d970f
-- statement:
--   The P2 M Global Theory Companion Theory Inert Doubling c T c T  9662d98d970f construction uses the P2 M Global Theory Companion Theory Inert Doubling c T c T  9662d98d970f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CompletionExists.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CompletionExists.lean#L53-L54

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

theorem P2M_GlobalTheory_CompanionTheory_InertDoubling_cT_cT__9662d98d970f (h : ∀ x, σ (σ x) = x) (M : Matrix m p L) : cT σ (cT σ M) = M := by sorry

alias «GlobalTheory».«CompanionTheory».«InertDoubling».«cT_cT'» := P2M_GlobalTheory_CompanionTheory_InertDoubling_cT_cT__9662d98d970f

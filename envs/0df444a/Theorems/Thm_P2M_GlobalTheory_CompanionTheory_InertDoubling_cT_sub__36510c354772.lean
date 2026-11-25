-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_InertDoubling_cT_sub__36510c354772
-- name    : P2M_GlobalTheory_CompanionTheory_InertDoubling_cT_sub__36510c354772
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:04:10.149591+00:00
-- url     : https://prove2.me/theorems/bfe0b662-aff3-4d81-9ed6-c79365792209
-- title:
--   P2 M Global Theory Companion Theory Inert Doubling c T sub  36510c354772: P2 M Global Theory Companion Theory Inert Doubling c T sub  36510c354772
-- statement:
--   The P2 M Global Theory Companion Theory Inert Doubling c T sub  36510c354772 construction uses the P2 M Global Theory Companion Theory Inert Doubling c T sub  36510c354772 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CompletionExists.lean#L44-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CompletionExists.lean#L44-L45

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

theorem P2M_GlobalTheory_CompanionTheory_InertDoubling_cT_sub__36510c354772 (M N : Matrix m p L) : cT σ (M - N) = cT σ M - cT σ N := by sorry

alias «GlobalTheory».«CompanionTheory».«InertDoubling».«cT_sub'» := P2M_GlobalTheory_CompanionTheory_InertDoubling_cT_sub__36510c354772

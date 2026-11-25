-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_InertDoubling_isInt_smul__901e0850cacc
-- name    : P2M_GlobalTheory_CompanionTheory_InertDoubling_isInt_smul__901e0850cacc
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:04:23.482109+00:00
-- url     : https://prove2.me/theorems/a317947b-3607-4bdc-9212-bb6959dbe881
-- title:
--   P2 M Global Theory Companion Theory Inert Doubling is Int smul  901e0850cacc: P2 M Global Theory Companion Theory Inert Doubling is Int smul  901e0850cacc
-- statement:
--   The P2 M Global Theory Companion Theory Inert Doubling is Int smul  901e0850cacc construction uses the P2 M Global Theory Companion Theory Inert Doubling is Int smul  901e0850cacc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CompletionExists.lean#L83-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CompletionExists.lean#L83-L84

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

theorem P2M_GlobalTheory_CompanionTheory_InertDoubling_isInt_smul__901e0850cacc {m p : Type} {A : Matrix m p L} {c : L} (hc : c ∈ intL L) (h : IsInt A) : IsInt (c • A) := by sorry

alias «GlobalTheory».«CompanionTheory».«InertDoubling».«isInt_smul'» := P2M_GlobalTheory_CompanionTheory_InertDoubling_isInt_smul__901e0850cacc
